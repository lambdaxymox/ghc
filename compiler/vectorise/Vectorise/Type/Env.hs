-- Vectorise a modules type and class declarations.
--
-- This produces new type constructors and family instances top be included in the module toplevel
-- as well as bindings for worker functions, dfuns, and the like.

module Vectorise.Type.Env ( 
  vectTypeEnv,
) where
  
#include "HsVersions.h"

import Vectorise.Env
import Vectorise.Vect
import Vectorise.Monad
import Vectorise.Builtins
import Vectorise.Type.TyConDecl
import Vectorise.Type.Classify
import Vectorise.Generic.PADict
import Vectorise.Generic.PAMethods
import Vectorise.Generic.PData
import Vectorise.Generic.Description
import Vectorise.Utils

import CoreSyn
import CoreUtils
import CoreUnfold
import DataCon
import TyCon
import CoAxiom
import Type
import FamInstEnv
import Id
import MkId
import NameEnv
import NameSet
import UniqFM
import OccName
import Unique

import Util
import Outputable
import DynFlags
import FastString
import MonadUtils

import Control.Monad
import Data.Maybe
import Data.List


-- Note [Pragmas to vectorise tycons]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- All imported type constructors that are not mapped to a vectorised type in the vectorisation map
-- (possibly because the defining module was not compiled with vectorisation) may be used in scalar
-- code encapsulated in vectorised code. If a such a type constructor 'T' is a member of the
-- 'Scalar' class (and hence also of 'PData' and 'PRepr'), it may also be used in vectorised code,
-- where 'T' represents itself, but the representation of 'T' still remains opaque in vectorised
-- code (i.e., it can only be used in scalar code).
--
-- An example is the treatment of 'Int'. 'Int's can be used in vectorised code and remain unchanged
-- by vectorisation.  However, the representation of 'Int' by the 'I#' data constructor wrapping an
-- 'Int#' is not exposed in vectorised code. Instead, computations involving the representation need
-- to be confined to scalar code.
--
-- VECTORISE pragmas for type constructors cover four different flavours of vectorising data type
-- constructors:
--
-- (1) Data type constructor 'T' that together with its constructors 'Cn' may be used in vectorised
--     code, where 'T' and the 'Cn' are automatically vectorised in the same manner as data types
--     declared in a vectorised module.  This includes the case where the vectoriser determines that
--     the original representation of 'T' may be used in vectorised code (as it does not embed any
--     parallel arrays.)  This case is for type constructors that are *imported* from a non-
--     vectorised module, but that we want to use with full vectorisation support.
--
--     An example is the treatment of 'Ordering' and '[]'.  The former remains unchanged by
--     vectorisation, whereas the latter is fully vectorised.
--
--     'PData' and 'PRepr' instances are automatically generated by the vectoriser.
--
--     Type constructors declared with {-# VECTORISE type T #-} are treated in this manner.
--
-- (2) Data type constructor 'T' that may be used in vectorised code, where 'T' is represented by an
--     explicitly given 'Tv', but the representation of 'T' is opaque in vectorised code (i.e., the
--     constructors of 'T' may not occur in vectorised code).  
--
--     An example is the treatment of '[::]'. The type '[::]' can be used in vectorised code and is
--     vectorised to 'PArray'. However, the representation of '[::]' is not exposed in vectorised
--     code. Instead, computations involving the representation need to be confined to scalar code.
--
--     'PData' and 'PRepr' instances need to be explicitly supplied for 'T' (they are not generated
--     by the vectoriser).
--
--     Type constructors declared with {-# VECTORISE type T = Tv #-} are treated in this manner
--     manner. (The vectoriser never treats a type constructor automatically in this manner.)
--
-- (3) Data type constructor 'T' that does not contain any parallel arrays and has explicitly
--     provided 'PData' and 'PRepr' instances (and maybe also a 'Scalar' instance), which together
--     with the type's constructors 'Cn' may be used in vectorised code. The type 'T' and its
--     constructors 'Cn' are represented by themselves in vectorised code.
--
--     An example is 'Bool', which is represented by itself in vectorised code (as it cannot embed
--     any parallel arrays).  However, we do not want any automatic generation of class and family
--     instances, which is why Case (1) does not apply.
--
--     'PData' and 'PRepr' instances need to be explicitly supplied for 'T' (they are not generated
--     by the vectoriser).
--
--     Type constructors declared with {-# VECTORISE SCALAR type T #-} are treated in this manner.
--
-- (4) Data type constructor 'T' that does not contain any parallel arrays and that, in vectorised
--     code, is represented by an explicitly given 'Tv', but the representation of 'T' is opaque in
--     vectorised code and 'T' is regarded to be scalar — i.e., it may be used in encapsulated
--     scalar subcomputations.
--
--     An example is the treatment of '(->)'. Types '(->)' can be used in vectorised code and are
--     vectorised to '(:->)'.  However, the representation of '(->)' is not exposed in vectorised
--     code. Instead, computations involving the representation need to be confined to scalar code
--     and may be part of encapsulated scalar computations.
--
--     'PData' and 'PRepr' instances need to be explicitly supplied for 'T' (they are not generated
--     by the vectoriser).
--
--     Type constructors declared with {-# VECTORISE SCALAR type T = Tv #-} are treated in this 
--     manner. (The vectoriser never treats a type constructor automatically in this manner.)
--
-- In addition, we have also got a single pragma form for type classes: {-# VECTORISE class C #-}.
-- It implies that the class type constructor may be used in vectorised code together with its data
-- constructor.  We generally produce a vectorised version of the data type and data constructor.
-- We do not generate 'PData' and 'PRepr' instances for class type constructors.  This pragma is the
-- default for all type classes declared in a vectorised module, but the pragma can also be used
-- explitly on imported classes.

-- Note [Vectorising classes]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We vectorise classes essentially by just vectorising their desugared Core representation, but we
-- do generate a 'Class' structure along the way (see 'Vectorise.Type.TyConDecl.vectTyConDecl').
--
-- Here is an example illustrating the mapping — assume
--
--   class Num a where
--     (+) :: a -> a -> a
--
-- It desugars to
--
--   data Num a = D:Num { (+) :: a -> a -> a }
--
-- which we vectorise to
--
--  data V:Num a = D:V:Num { ($v+) :: PArray a :-> PArray a :-> PArray a }
--
-- while adding the following entries to the vectorisation map:
--
--   tycon  : Num   --> V:Num
--   datacon: D:Num --> D:V:Num
--   var    : (+) --> ($v+)

-- |Vectorise type constructor including class type constructors.
--
vectTypeEnv :: [TyCon]                   -- Type constructors defined in this module
            -> [CoreVect]                -- All 'VECTORISE [SCALAR] type' declarations in this module
            -> [CoreVect]                -- All 'VECTORISE class' declarations in this module
            -> VM ( [TyCon]              -- old TyCons ++ new TyCons
                  , [FamInst Unbranched] -- New type family instances.
                  , [(Var, CoreExpr)])   -- New top level bindings.
vectTypeEnv tycons vectTypeDecls vectClassDecls
  = do { traceVt "** vectTypeEnv" $ ppr tycons

       ; let   -- {-# VECTORISE type T -#} (ONLY the imported tycons)
             impVectTyCons          = (   [tycon | VectType False tycon Nothing <- vectTypeDecls]
                                       ++ [tycon | VectClass tycon              <- vectClassDecls])
                                      \\ tycons
               
               -- {-# VECTORISE type T = Tv -#} (imported & local tycons with an /RHS/)
             vectTyConsWithRHS      = [ (tycon, rhs)
                                      | VectType False tycon (Just rhs) <- vectTypeDecls]

               -- {-# VECTORISE SCALAR type T = Tv -#} (imported & local tycons with an /RHS/)
             scalarTyConsWithRHS    = [ (tycon, rhs) 
                                      | VectType True  tycon (Just rhs) <- vectTypeDecls]

               -- {-# VECTORISE SCALAR type T -#} (imported & local /scalar/ tycons without an RHS)
             scalarTyConsNoRHS      = [tycon | VectType True tycon Nothing <- vectTypeDecls]

               -- Check that is not a VECTORISE SCALAR tycon nor VECTORISE tycons with explicit rhs?
             vectSpecialTyConNames  = mkNameSet . map tyConName $ 
                                        scalarTyConsNoRHS ++ 
                                        map fst (vectTyConsWithRHS ++ scalarTyConsWithRHS)
             notVectSpecialTyCon tc = not $ (tyConName tc) `elemNameSet` vectSpecialTyConNames

         -- Build a map containing all vectorised type constructor. If the vectorised type
         -- constructor differs from the original one, then it is mapped to 'True'; if they are
         -- both the same, then it maps to 'False'.
       ; vectTyCons          <- globalVectTyCons
       ; let vectTyConBase    = mapUFM_Directly isDistinct vectTyCons    -- 'True' iff tc /= V[[tc]]
             isDistinct u tc  = u /= getUnique tc
             vectTyConFlavour = vectTyConBase 
                                `plusNameEnv` 
                                mkNameEnv [ (tyConName tycon, True) 
                                          | (tycon, _) <- vectTyConsWithRHS ++ scalarTyConsWithRHS]
                                `plusNameEnv`
                                mkNameEnv [ (tyConName tycon, False)  -- original representation
                                          | tycon <- scalarTyConsNoRHS]
                                            

           -- Split the list of 'TyCons' into the ones (1) that we must vectorise and those (2)
           -- that we could, but don't need to vectorise.  Type constructors that are not data
           -- type constructors or use non-Haskell98 features are being dropped.  They may not
           -- appear in vectorised code.  (We also drop the local type constructors appearing in a
           -- VECTORISE SCALAR pragma or a VECTORISE pragma with an explicit right-hand side, as
           -- these are being handled separately.  NB: Some type constructors may be marked SCALAR
           -- /and/ have an explicit right-hand side.)
           --
           -- Furthermore, 'par_tcs' are those type constructors (converted or not) whose
           -- definition, directly or indirectly, depends on parallel arrays. Finally, 'drop_tcs'
           -- are all type constructors that cannot be vectorised.
       ; parallelTyCons <- (`addListToNameSet` map (tyConName . fst) vectTyConsWithRHS) <$>
                             globalParallelTyCons
       ; let maybeVectoriseTyCons = filter notVectSpecialTyCon tycons ++ impVectTyCons
             (conv_tcs, keep_tcs, par_tcs, drop_tcs)
               = classifyTyCons vectTyConFlavour parallelTyCons maybeVectoriseTyCons

       ; traceVt " known parallel : " $ ppr parallelTyCons
       ; traceVt " VECT SCALAR    : " $ ppr (scalarTyConsNoRHS ++ map fst scalarTyConsWithRHS)
       ; traceVt " VECT [class]   : " $ ppr impVectTyCons
       ; traceVt " VECT with rhs  : " $ ppr (map fst (vectTyConsWithRHS ++ scalarTyConsWithRHS))
       ; traceVt " -- after classification (local and VECT [class] tycons) --" empty
       ; traceVt " reuse          : " $ ppr keep_tcs
       ; traceVt " convert        : " $ ppr conv_tcs
       
           -- warn the user about unvectorised type constructors
       ; let explanation    = ptext (sLit "(They use unsupported language extensions") $$
                              ptext (sLit "or depend on type constructors that are not vectorised)")
             drop_tcs_nosyn = filter (not . isSynTyCon) drop_tcs
       ; unless (null drop_tcs_nosyn) $
           emitVt "Warning: cannot vectorise these type constructors:" $ 
             pprQuotedList drop_tcs_nosyn $$ explanation

       ; mapM_ addParallelTyConAndCons $ par_tcs ++ map fst vectTyConsWithRHS

       ; let mapping =      
                    -- Type constructors that we found we don't need to vectorise and those
                    -- declared VECTORISE SCALAR /without/ an explicit right-hand side, use the same
                    -- representation in both unvectorised and vectorised code; they are not
                    -- abstract.
                  [(tycon, tycon, False) | tycon <- keep_tcs ++ scalarTyConsNoRHS]
                    -- We do the same for type constructors declared VECTORISE SCALAR /without/
                    -- an explicit right-hand side
               ++ [(tycon, vTycon, True) | (tycon, vTycon) <- vectTyConsWithRHS ++ scalarTyConsWithRHS]
       ; syn_tcs <- catMaybes <$> mapM defTyConDataCons mapping

           -- Vectorise all the data type declarations that we can and must vectorise (enter the
           -- type and data constructors into the vectorisation map on-the-fly.)
       ; new_tcs <- vectTyConDecls conv_tcs
       
       ; let dumpTc tc vTc = traceVt "---" (ppr tc <+> text "::" <+> ppr (dataConSig tc) $$
                                            ppr vTc <+> text "::" <+> ppr (dataConSig vTc))
             dataConSig tc | Just dc <- tyConSingleDataCon_maybe tc = dataConRepType dc
                           | otherwise                              = panic "dataConSig"
       ; zipWithM_ dumpTc (filter isClassTyCon conv_tcs) (filter isClassTyCon new_tcs)

           -- We don't need new representation types for dictionary constructors. The constructors
           -- are always fully applied, and we don't need to lift them to arrays as a dictionary
           -- of a particular type always has the same value.
       ; let orig_tcs = filter (not . isClassTyCon) $ keep_tcs ++ conv_tcs
             vect_tcs = filter (not . isClassTyCon) $ keep_tcs ++ new_tcs

           -- Build 'PRepr' and 'PData' instance type constructors and family instances for all
           -- type constructors with vectorised representations.
       ; reprs      <- mapM tyConRepr vect_tcs
       ; repr_fis   <- zipWith3M buildPReprTyCon  orig_tcs vect_tcs reprs
       ; pdata_fis  <- zipWith3M buildPDataTyCon  orig_tcs vect_tcs reprs
       ; pdatas_fis <- zipWith3M buildPDatasTyCon orig_tcs vect_tcs reprs

       ; let fam_insts  = repr_fis ++ pdata_fis ++ pdatas_fis
             repr_axs   = map famInstAxiom repr_fis
             pdata_tcs  = famInstsRepTyCons pdata_fis
             pdatas_tcs = famInstsRepTyCons pdatas_fis
             
       ; updGEnv $ extendFamEnv fam_insts

           -- Generate workers for the vectorised data constructors, dfuns for the 'PA' instances of
           -- the vectorised type constructors, and associate the type constructors with their dfuns
           -- in the global environment.  We get back the dfun bindings (which we will subsequently
           -- inject into the modules toplevel).
       ; (_, binds) <- fixV $ \ ~(dfuns, _) ->
           do { defTyConPAs (zipLazy vect_tcs dfuns)

                  -- Query the 'PData' instance type constructors for type constructors that have a
                  -- VECTORISE SCALAR type pragma without an explicit right-hand side (this is Item
                  --  (3) of "Note [Pragmas to vectorise tycons]" above).
              ; pdata_scalar_tcs <- mapM pdataReprTyConExact scalarTyConsNoRHS

                  -- Build workers for all vectorised data constructors (except abstract ones)
              ; sequence_ $
                  zipWith3 vectDataConWorkers (orig_tcs  ++ scalarTyConsNoRHS)
                                              (vect_tcs  ++ scalarTyConsNoRHS)
                                              (pdata_tcs ++ pdata_scalar_tcs)

                  -- Build a 'PA' dictionary for all type constructors (except abstract ones & those
                  -- defined with an explicit right-hand side where the dictionary is user-supplied)
              ; dfuns <- sequence $
                           zipWith4 buildTyConPADict
                                    vect_tcs
                                    repr_axs
                                    pdata_tcs
                                    pdatas_tcs

              ; binds <- takeHoisted
              ; return (dfuns, binds)
              }

           -- Return the vectorised variants of type constructors as well as the generated instance
           -- type constructors, family instances, and dfun bindings.
       ; return ( new_tcs ++ pdata_tcs ++ pdatas_tcs ++ syn_tcs
                , fam_insts, binds)
       }
  where
    addParallelTyConAndCons tycon
      = do
        { addGlobalParallelTyCon tycon
        ; mapM_ addGlobalParallelVar . concatMap dataConImplicitIds . tyConDataCons $ tycon
        }

    -- Add a mapping from the original to vectorised type constructor to the vectorisation map.  
    -- Unless the type constructor is abstract, also mappings from the orignal's data constructors
    -- to the vectorised type's data constructors.
    --
    -- We have three cases: (1) original and vectorised type constructor are the same, (2) the
    -- name of the vectorised type constructor is canonical (as prescribed by 'mkVectTyConOcc'), or
    -- (3) the name is not canonical.  In the third case, we additionally introduce a type synonym
    -- with the canonical name that is set equal to the non-canonical name (so that we find the
    -- right type constructor when reading vectorisation information from interface files).
    --
    defTyConDataCons (origTyCon, vectTyCon, isAbstract)
      = do
        { canonName <- mkLocalisedName mkVectTyConOcc origName
        ; if    origName == vectName                             -- Case (1)
             || vectName == canonName                            -- Case (2)
          then do 
          { defTyCon origTyCon vectTyCon                         -- T  --> vT
          ; defDataCons                                          -- Ci --> vCi
          ; return Nothing
          }
          else do                                                 -- Case (3)
          { let synTyCon = mkSyn canonName (mkTyConTy vectTyCon)  -- type S = vT
          ; defTyCon origTyCon synTyCon                           -- T  --> S
          ; defDataCons                                           -- Ci --> vCi
          ; return $ Just synTyCon
          }
        }
      where
        origName  = tyConName origTyCon
        vectName  = tyConName vectTyCon

        mkSyn canonName ty = mkSynTyCon canonName (typeKind ty) [] (SynonymTyCon ty) NoParentTyCon
        
        defDataCons
          | isAbstract = return ()
          | otherwise  
          = do { MASSERT(length (tyConDataCons origTyCon) == length (tyConDataCons vectTyCon))
               ; zipWithM_ defDataCon (tyConDataCons origTyCon) (tyConDataCons vectTyCon)
               }


-- Helpers --------------------------------------------------------------------

buildTyConPADict :: TyCon -> CoAxiom Unbranched -> TyCon -> TyCon -> VM Var
buildTyConPADict vect_tc prepr_ax pdata_tc pdatas_tc
 = tyConRepr vect_tc >>= buildPADict vect_tc prepr_ax pdata_tc pdatas_tc

-- Produce a custom-made worker for the data constructors of a vectorised data type.  This includes
-- all data constructors that may be used in vectorised code — i.e., all data constructors of data
-- types with 'VECTORISE [SCALAR] type' pragmas with an explicit right-hand side.  Also adds a mapping
-- from the original to vectorised worker into the vectorisation map.
--
-- FIXME: It's not nice that we need create a special worker after the data constructors has
--   already been constructed.  Also, I don't think the worker is properly added to the data
--   constructor.  Seems messy.
vectDataConWorkers :: TyCon -> TyCon -> TyCon -> VM ()
vectDataConWorkers orig_tc vect_tc arr_tc
  = do { traceVt "Building vectorised worker for datatype" (ppr orig_tc)
  
       ; bs <- sequence
             . zipWith3 def_worker  (tyConDataCons orig_tc) rep_tys
             $ zipWith4 mk_data_con (tyConDataCons vect_tc)
                                    rep_tys
                                    (inits rep_tys)
                                    (tail $ tails rep_tys)
        ; mapM_ (uncurry hoistBinding) bs
        }
  where
    tyvars   = tyConTyCoVars vect_tc
    var_tys  = mkTyCoVarTys tyvars
    ty_args  = map Type var_tys
    res_ty   = mkTyConApp vect_tc var_tys

    cons     = tyConDataCons vect_tc
    arity    = length cons
    [arr_dc] = tyConDataCons arr_tc

    rep_tys  = map dataConRepArgTys $ tyConDataCons vect_tc

    mk_data_con con tys pre post
      = do dflags <- getDynFlags
           liftM2 (,) (vect_data_con con)
                      (lift_data_con tys pre post (mkDataConTag dflags con))

    sel_replicate len tag
      | arity > 1 = do
                      rep <- builtin (selReplicate arity)
                      return [rep `mkApps` [len, tag]]

      | otherwise = return []

    vect_data_con con = return $ mkConApp con ty_args
    lift_data_con tys pre_tys post_tys tag
      = do
          len  <- builtin liftingContext
          args <- mapM (newLocalVar (fsLit "xs"))
                  =<< mapM mkPDataType tys

          sel  <- sel_replicate (Var len) tag

          pre   <- mapM emptyPD (concat pre_tys)
          post  <- mapM emptyPD (concat post_tys)

          return . mkLams (len : args)
                 . wrapFamInstBody arr_tc var_tys
                 . mkConApp arr_dc
                 $ ty_args ++ sel ++ pre ++ map Var args ++ post

    def_worker data_con arg_tys mk_body
      = do
          arity <- polyArity tyvars
          body <- closedV
                . inBind orig_worker
                . polyAbstract tyvars $ \args ->
                  liftM (mkLams (tyvars ++ args) . vectorised)
                $ buildClosures tyvars [] [] arg_tys res_ty mk_body

          raw_worker <- mkVectId orig_worker (exprType body)
          let vect_worker = raw_worker `setIdUnfolding`
                              mkInlineUnfolding (Just arity) body
          defGlobalVar orig_worker vect_worker
          return (vect_worker, body)
      where
        orig_worker = dataConWorkId data_con

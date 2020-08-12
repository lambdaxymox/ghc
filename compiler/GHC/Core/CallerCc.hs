{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TupleSections #-}

module GHC.Core.CallerCc (addCallerCcs) where

import Data.Maybe
import Data.Data
import qualified Data.Generics as SYB
import GHC.Generics

import Control.Monad.Trans.State.Strict
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Binary as B
import Data.List (intercalate)

import GHC
import GHC.Prelude
import GHC.Serialized
import GHC.Utils.Outputable
import GHC.Types.CostCentre
import GHC.Types.CostCentre.State
import GHC.Core

addCallerCcs :: DynFlags -> ModGuts -> ModGuts
addCallerCcs dflags guts = do
  let env :: Env
      env = Env
        { thisModule = mg_module guts
        , ccState = newCostCentreState
        , dflags = dflags
        , revParents = []
        }
  in guts { mg_binds = doCoreProgram env (mg_binds guts)
          , mg_anns = anns'
          }

doCoreProgram :: Env -> CoreProgram -> CoreProgram
doCoreProgram env binds = flip evalState newCostCentreState $ do
    mapM (doBind env) binds

doBind :: Env -> CoreBind -> M CoreBind
doBind env (NonRec b rhs) = NonRec b <$> doExpr (addParent b env) rhs
doBind env (Rec bs) = Rec <$> mapM doPair bs
  where
    doPair (b,rhs) = (b,) <$> doExpr (addParent b env) rhs

doExpr :: Env -> CoreExpr -> M CoreExpr
doExpr env e@(Var v)
  | needsCallSiteCostCentre env v = do
    let nameDoc :: SDoc
        nameDoc = fsep (punctuate dot (map ppr (parents env))) <> parens (text "calling " <> ppr v)

        ccName :: CcName
        ccName = mkFastString $ showSDoc (dflags env) nameDoc
    ccIdx <- getCCIndex' ccName
    let span = case revParents env of
          top:_ -> nameSrcSpan $ varName top
          _     -> noSrcSpan
        cc = NormalCC (ExprCC ccIdx) ccName (thisModule env) span
        tick :: Tickish Id
        tick = ProfNote cc True True
    pure $ Tick tick e
  | otherwise = pure e
doExpr env e@(Lit _)        = pure e
doExpr env (f `App` x)      = App <$> doExpr env f <*> doExpr env x
doExpr env (Lam b x)        = Lam b <$> doExpr env x
doExpr env (Let b rhs)      = Let <$> doBind env b <*> doExpr env rhs
doExpr env (Case scrut b ty alts) =
    Case <$> doExpr env scrut <*> pure b <*> pure ty <*> mapM doAlt alts
  where
    doAlt (con, bs, rhs) = (con, bs,) <$> doExpr env rhs
doExpr env (Cast expr co)   = Cast <$> doExpr env expr <*> pure co
doExpr env (Tick t e)       = Tick t <$> doExpr env e
doExpr env e@(Type _)       = pure e
doExpr env e@(Coercion _)   = pure e

type M = State CostCentreState

getCCIndex' :: FastString -> M CostCentreIndex
getCCIndex' name = state (getCCIndex name)

data Env = Env
  { thisModule  :: !Module
  , dflags      :: !DynFlags
  , ccState     :: !CostCentreState
  , revParents  :: [Id]
  }

addParent :: Id -> Env -> Env
addParent i env = env { revParents = i : revParents env }

parents :: Env -> [Id]
parents env = reverse (revParents env)

needsCallSiteCostCentre :: Env -> Id -> Bool
needsCallSiteCostCentre env i =
  case callerCcInfo $ idInfo i of
    WantsCallerCc -> True
    NoCallerCc    -> False

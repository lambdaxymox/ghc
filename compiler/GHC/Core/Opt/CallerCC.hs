{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TupleSections #-}

module GHC.Core.Opt.CallerCC
    ( addCallerCostCentres
    , CallerCcFilter
    , parseCallerCcFilter
    ) where

import Data.Bifunctor
import Data.Data
import Data.Maybe
import qualified Text.Parsec as P

import Control.Applicative
import Control.Monad.Trans.State.Strict
import qualified Data.ByteString.Lazy as BSL
import Data.List (intercalate)
import Data.Either
import Control.Monad

import GHC.Prelude
import GHC.Utils.Outputable as Outputable
import GHC.Driver.Session
import GHC.Driver.Types
import GHC.Driver.Ppr
import GHC.Types.CostCentre
import GHC.Types.CostCentre.State
import GHC.Types.Name hiding (varName)
import GHC.Unit.Module.Name
import GHC.Types.SrcLoc
import GHC.Types.Var
import GHC.Unit.Types
import GHC.Data.FastString
import GHC.Types.Id.Info
import GHC.Core
import GHC.Core.Opt.Monad

import GHC.Prelude

addCallerCostCentres :: ModGuts -> CoreM ModGuts
addCallerCostCentres guts = do
  dflags <- getDynFlags
  let filters = callerCcFilters dflags
  let env :: Env
      env = Env
        { thisModule = mg_module guts
        , ccState = newCostCentreState
        , dflags = dflags
        , revParents = []
        , filters = filters
        }
  let guts' = guts { mg_binds = doCoreProgram env (mg_binds guts)
                   }
  return guts'

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
        nameDoc = fcat (punctuate dot (map ppr (parents env))) <> parens (text "calling " <> ppr v)

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
  { thisModule  :: Module
  , dflags      :: DynFlags
  , ccState     :: CostCentreState
  , revParents  :: [Id]
  , filters     :: [CallerCcFilter]
  }

addParent :: Id -> Env -> Env
addParent i env = env { revParents = i : revParents env }

parents :: Env -> [Id]
parents env = reverse (revParents env)

needsCallSiteCostCentre :: Env -> Id -> Bool
needsCallSiteCostCentre env i =
    any matches (filters env)
  where
    matches :: CallerCcFilter -> Bool
    matches ccf =
        checkModule && checkFunc
      where
        checkModule =
          case ccfModuleName ccf of
            Just modFilt
              | Just iMod <- nameModule_maybe (varName i)
              -> moduleName iMod == modFilt
              | otherwise -> False
            Nothing -> True
        checkFunc =
            occNameMatches (ccfFuncName ccf) (getOccName i)

    iMod = nameModule_maybe (varName i)

data NamePattern
    = PChar Char NamePattern
    | PWildcard NamePattern
    | PEnd

instance Outputable NamePattern where
  ppr (PChar c rest) = char c <> ppr rest
  ppr (PWildcard rest) = char '*' <> ppr rest
  ppr PEnd = Outputable.empty

occNameMatches :: NamePattern -> OccName -> Bool
occNameMatches pat = go pat . occNameString
  where
    go :: NamePattern -> String -> Bool
    go PEnd "" = True
    go (PChar c rest) (d:s)
      = d == c && go rest s
    go (PWildcard rest) s
      = go rest s || go (PWildcard rest) (tail s)
    go _ _  = False

type Parser = P.Parsec String ()

parseNamePattern :: Parser NamePattern
parseNamePattern = wildcard <|> char <|> end
  where
    wildcard = do
      P.char '*'
      PWildcard <$> parseNamePattern
    char = PChar <$> P.anyChar <*> parseNamePattern
    end = PEnd <$ P.eof

data CallerCcFilter
    = CallerCcFilter { ccfModuleName  :: Maybe ModuleName
                     , ccfFuncName    :: NamePattern
                     }

instance Outputable CallerCcFilter where
  ppr ccf =
    maybe (char '*') ppr (ccfModuleName ccf)
    <> char '.'
    <> ppr (ccfFuncName ccf)

parseCallerCcFilter :: String -> Either String CallerCcFilter
parseCallerCcFilter =
    first show . P.parse parseCallerCcFilter' "caller-CC filter"

parseCallerCcFilter' :: Parser CallerCcFilter
parseCallerCcFilter' =
  CallerCcFilter
    <$> moduleFilter
    <*  P.char '.'
    <*> parseNamePattern
  where
    moduleFilter :: Parser (Maybe ModuleName)
    moduleFilter =
      (Just . mkModuleName <$> moduleName)
      <|>
      (Nothing <$ P.char '*')

    moduleName :: Parser String
    moduleName = do
      c <- P.upper
      cs <- some $ P.upper <|> P.lower <|> P.digit <|> P.oneOf "_"
      rest <- optional $ P.try $ P.char '.' >> fmap ('.':) moduleName
      return $ c : (cs ++ fromMaybe "" rest)


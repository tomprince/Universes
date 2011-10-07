{-# LANGUAGE DeriveFunctor, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
{-# OPTIONS -fwarn-unused-imports #-}
module Base (Sort(..), Term(..), Binding(..), Context(..), emptyContext, fromIntSort, toIntSort, dbShift) where

import Data.Function(on)

class Eq s => Sort s where
    triple :: s -> s -> s
    raise :: s -> s
    sort :: Int -> s
    toInt :: s -> Int

data Term s
  = Free String
  | Var Int
  | Forall (Maybe String) (Term s) (Term s)
  | Lambda (Maybe String) (Term s) (Term s)
  | Apply (Term s) (Term s)
  | Sort s
    deriving (Eq, Functor)

data Binding s
  = Bind (Term s)
  | LetBind (Term s) (Term s)
    deriving (Eq)

deriving instance Show (Term s) => Show (Binding s)

data Context s = Context { freeVars :: [(String, Binding s)], boundVars :: [Binding s] }

emptyContext :: Context s
emptyContext = Context [] []

fromIntSort :: Sort s => Term Int -> Term s
fromIntSort = fmap sort

toIntSort :: Sort s => Term s -> Term Int
toIntSort = fmap toInt

dbShift :: Int -> Term s -> Term s
dbShift n = shift
    where
      shift v@(Free _) = v
      shift (Var i) = Var $ n + i
      shift (Forall s t t') = (Forall s `on` shift) t t'
      shift (Lambda s t t') = (Lambda s `on` shift) t t'
      shift (Apply t t') = (Apply `on` shift) t t'
      shift s@(Sort _) = s

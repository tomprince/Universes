{-# LANGUAGE DeriveFunctor #-}
module Base (Sort(..), Term(..), Binding(..), Context(..), fromIntSort) where

import Data.Function(on)

class Eq s => Sort s where
    triple :: s -> s -> s
    raise :: s -> s
    sort :: Int -> s

data Term s
  = Free String
  | Var Int
  | Forall (Term s) (Term s)
  | Lambda (Term s) (Term s)
  | Apply (Term s) (Term s)
  | Sort s
    deriving (Eq, Show, Functor)

data Binding s
  = Bind (Term s)
  | LetBind (Term s) (Term s)
    deriving (Eq, Show)

type Context s = ([(String, Binding s)], [Binding s])

fromIntSort :: Sort s => Term Int -> Term s
fromIntSort = fmap sort

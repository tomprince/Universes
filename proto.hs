{-# LANGUAGE DeriveDataTypeable, GADTs, Rank2Types #-}

import Data.Generics.Zipper
import Data.Generics
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Sequence(Seq,(|>))
import qualified Data.Sequence as Seq
import Control.Monad
import Data.Maybe
import Data.Tuple
import Data.Function

data Sort
  = Prop
  | Type Int
    deriving (Eq, Show, Typeable, Data)

data Term
  = Free String
  | Var Int
  | Forall Term Term
  | Lambda Term Term
  | Apply Term Term
  | Sort Sort
    deriving (Eq, Show, Typeable, Data)

data Binding
  = Bind Term
  | LetBind Term Term
    deriving (Eq, Show, Typeable, Data)

type Context = ([(String, Binding)], [Binding])

maybeT :: (a -> Maybe a) -> a -> a
maybeT f a = fromMaybe a (f a)
    
getLetValue :: Binding -> Maybe Term
getLetValue (LetBind c _) = Just c
getLetValue _ = Nothing

getType :: Binding -> Term
getType (LetBind _ t) = t
getType (Bind t) = t

idx :: Int -> [a] -> Maybe a
idx 0 (x:xs) = Just x
idx i (x:xs) | i > 0 = idx (i-1) xs
idx _ _ = Nothing

fromCtx :: Context -> Term -> Maybe Binding
fromCtx ctx (Free v) = lookup v (fst ctx)
fromCtx ctx (Var i) = idx i (snd ctx)
fromCtx _ _ = Nothing

lift :: Context -> Term -> Context
lift ctx t = (fst ctx, Bind t : snd ctx)
liftL ctx t = (fst ctx, LetBind t (fromJust $ typer ctx t) : snd ctx)

isKind :: Term -> Bool
isKind (Sort _) = True
isKind _ = False

kind :: Term -> Maybe Sort
kind (Sort s) = Just s
kind _ = Nothing

triple :: Sort -> Sort -> Sort
triple Prop Prop = Type 0
triple (Type i) (Type j) = Type $ max i j
triple Prop (Type i) = Type (i+1)
triple (Type i) Prop = Prop
             
raise :: Sort -> Sort
raise Prop = Type 0
raise (Type i) = Type (i+1)

eval :: Context -> Term -> Maybe Term
eval ctx v@(Free _) = return $ maybeT ((getLetValue =<<) . fromCtx ctx) v
eval ctx v@(Var _)  = return $ maybeT ((getLetValue =<<) . fromCtx ctx) v
eval ctx (Lambda v t) = liftM2 Lambda (eval ctx v) (eval (lift ctx v) t)
eval ctx (Forall v t) = liftM2 Forall (eval ctx v) (eval (lift ctx v) t)
eval ctx (Apply f v) = do f <- eval ctx f
                          v <- eval ctx v
                          case f of
                                Lambda _ t -> eval (liftL ctx v) t
                                _ -> return $ Apply f v
eval ctx s@(Sort _) = return s
                 
simpl :: Context -> Term -> Term
simpl ctx = maybeT ((getLetValue =<<) . fromCtx ctx)

comp :: Context -> Term -> Term -> Bool
comp ctx t t' = fromMaybe False $ (liftM2 (==) `on` eval ctx) t t'

typer :: Context -> Term -> Maybe Term
typer ctx v@(Free _) = liftM getType $ fromCtx ctx v
typer ctx v@(Var _)  = liftM getType $ fromCtx ctx v
typer ctx (Lambda v t) = do t' <- typer ctx v
                            v' <- eval ctx v
                            guard =<< isKind `liftM` eval ctx t'
                            t <- typer (lift ctx v') t
                            return $ Forall v t
typer ctx (Forall v t) = do v <- typer ctx v
                            let ctx' = lift ctx v
                            t' <- typer ctx' t
                            guard =<< isKind `liftM` eval ctx t'
                            k <- (liftM2 triple `on` kind) v t'
                            return $ Sort k
typer ctx (Apply f v) = do f <- eval ctx f
                           t_v <- typer ctx v
                           case f of
                             Lambda v t -> do guard $ comp ctx t_v v
                                              typer (liftL ctx v) t
                             _ -> Nothing
typer ctx (Sort s) = return $ Sort $ raise s

data Ctx = L Term | B Term
add_to_context :: Context -> (String, Ctx) -> Context
add_to_context ctx (name, B t) = fromJust $ typer ctx t >> return ((name, Bind t) : fst ctx, snd ctx)
add_to_context ctx (name, L t) = fromJust $ typer ctx t >>= \t' -> return  ((name, LetBind t t') : fst ctx, snd ctx)
  
build_context :: [(String, Ctx)] -> Context
build_context = foldl add_to_context ([],[])
                
context = build_context [ ("Prop", L (Sort$Prop))
                        , ("Power", L (Lambda (Sort$Type 1) (Forall (Var 0) (Free "Prop"))))
                        , ("False", L (Forall (Free "Prop") (Var 0)))
                        , ("Not", L (Lambda (Sort$Type 1) (Forall (Var 0) (Free "False"))))
                        , ("U", L (Forall (Sort$Prop) (Forall (Forall (p $ p $ Var 0) (Var 1)) (p $ p $ Var 1))))
                        ]
  where p x = (Apply (Free "Power") x)
                                    
                                                      

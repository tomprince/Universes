import Control.Arrow
import Control.Monad
import Data.Function
import Data.Maybe
import Data.Tuple

import Base
import Parser
import Pretty

data S
  = Prop
  | Type Int
    deriving (Eq, Show)

instance Sort S where
    triple Prop Prop = Type 0
    triple (Type i) (Type j) = Type $ max i j
    triple Prop (Type i) = Type (i+1)
    triple (Type i) Prop = Prop

    raise Prop = Type 0
    raise (Type i) = Type (i+1)

    sort n | n > 0     = Type (n-1)
           | otherwise = Prop
    toInt Prop = 0
    toInt (Type i) = i+1

data S' = Type'
    deriving (Eq, Show)

instance Sort S' where
    triple Type' Type' = Type'
    raise Type' = Type'
    sort _ = Type'
    toInt _ = 0

maybeT :: (a -> Maybe a) -> a -> a
maybeT f a = fromMaybe a (f a)

getLetValue :: Binding s -> Maybe (Term s)
getLetValue (LetBind c _) = Just c
getLetValue _ = Nothing

getType :: Binding s -> Term s
getType (LetBind _ t) = t
getType (Bind t) = t

idx :: Int -> [a] -> Maybe a
idx 0 (x:xs) = Just x
idx i (x:xs) | i > 0 = idx (i-1) xs
idx _ _ = Nothing

fromCtx :: Context s -> Term s -> Maybe (Binding s)
fromCtx ctx (Free v) = lookup v (freeVars ctx)
fromCtx ctx (Var i) = idx i (boundVars ctx)
fromCtx _ _ = Nothing

lift :: Context s -> Term s -> Context s
lift ctx t = ctx { boundVars =  Bind t : boundVars ctx }
liftL ctx t = ctx { boundVars = LetBind t (fromJust $ typer ctx t) : boundVars ctx }

isKind :: Sort s => Term s -> Bool
isKind (Sort _) = True
isKind _ = False

kind :: Sort s => Term s -> Maybe s
kind (Sort s) = Just s
kind _ = Nothing

eval :: Sort s => Context s -> Term s -> Maybe (Term s)
eval ctx v@(Free _) = return $ maybeT ((getLetValue =<<) . fromCtx ctx) v
eval ctx v@(Var _)  = return $ maybeT ((getLetValue =<<) . fromCtx ctx) v
eval ctx (Lambda id v t) = liftM2 (Lambda id) (eval ctx v) (eval (lift ctx v) t)
eval ctx (Forall id v t) = liftM2 (Forall id) (eval ctx v) (eval (lift ctx v) t)
eval ctx (Apply f v) = do f <- eval ctx f
                          v <- eval ctx v
                          case f of
                                Lambda _ _ t -> eval (liftL ctx v) t
                                _ -> return $ Apply f v
eval ctx s@(Sort _) = return s

simpl :: Context s -> Term s -> Term s
simpl ctx = maybeT ((getLetValue =<<) . fromCtx ctx)

comp :: Sort s => Context s -> Term s -> Term s -> Bool
comp ctx t t' = fromMaybe False $ (liftM2 (==) `on` eval ctx) t t'

typer :: Sort s => Context s -> Term s -> Maybe (Term s)
typer ctx v@(Free _) = liftM getType $ fromCtx ctx v
typer ctx v@(Var _)  = liftM getType $ fromCtx ctx v
typer ctx (Lambda id v t) = do t' <- typer ctx v
                               v' <- eval ctx v
                               guard =<< isKind `liftM` eval ctx t'
                               t <- typer (lift ctx v') t
                               return $ Forall id v t
typer ctx (Forall _ v t) = do v <- typer ctx v
                              let ctx' = lift ctx v
                              t' <- typer ctx' t
                              guard =<< isKind `liftM` eval ctx t'
                              k <- (liftM2 triple `on` kind) v t'
                              return $ Sort k
typer ctx (Apply f v) = do f <- eval ctx f
                           t_v <- typer ctx v
                           case f of
                             Lambda _ v t -> do guard $ comp ctx t_v v
                                                typer (liftL ctx v) t
                             _ -> Nothing
typer ctx (Sort s) = return $ Sort $ raise s

data Ctx s = L (Term s) | B (Term s)
addToContext :: Sort s => Context s -> (String, Ctx s) -> Maybe (Context s)
addToContext ctx (name, B t) = typer ctx t >> return  ctx { freeVars = (name, Bind t) : freeVars ctx}
addToContext ctx (name, L t) = typer ctx t >>= \t' -> return ctx { freeVars = (name, LetBind t t') : freeVars ctx}

buildContext :: Sort s => [(String, Ctx s)] -> Context s
buildContext = foldl (\ctx -> fromMaybe ctx . addToContext ctx) emptyContext

context :: Sort s => Context s
context = buildContext [ ("Prop", l "%0"), ("Type", l "%1")
                        , ("Power", l "\\P: Type, P -> Prop")
                        , ("False", l "forall P: Prop, P")
                        , ("Not", l "\\P : Prop, P -> False")
                        , ("U", l "forall (T: Type) (_: (Power (Power T)) -> T), Power (Power T)")
                        ]
          where l = L . parsed

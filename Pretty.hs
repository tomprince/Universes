module Pretty () where

import Base

import Control.Monad.Reader
import Data.List
import Data.Maybe
import Control.Applicative
import Control.Arrow
import Control.Monad

type DBContext = [String]

extend :: String -> DBContext -> DBContext
extend = (:)

find :: DBContext -> String -> Term s
find ctx id = maybe (Free id) Var (elemIndex id ctx)

fresh :: Maybe String -> Reader DBContext t -> Reader DBContext (String, t)
fresh hint cont = do ctx <- ask
                     let id = head $ filter (not . flip elem ctx) $ map (fromMaybe "x" hint ++) $ [""] ++ map show [1..]
                     cont <- local (id:) cont
                     return (id, cont)


freshL :: [Maybe String] -> Reader DBContext t -> Reader DBContext ([String], t)
freshL (hint:hints) cont = fresh hint (freshL hints cont) >>= return . zip
    where zip (id,(ids,cont)) = (id:ids,cont)
freshL [] cont = (,) [] <$> cont

localAsk :: MonadReader r m => (r -> (t, r)) -> (t -> m s) -> m s
localAsk m r = asks m >>= \(t, s) -> local (const s) (r t)

(<++>) :: Monad m => m [a] -> m [a] -> m [a]
(<++>) = liftM2 (++)

--printAbs :: String -> Maybe String -> Term Int -> Term Int -> Reader DBContext String
--printAbs abs id t t' = do (id, ctx) <- asks $ fresh id
--                          t <- pprint t
--                          return ("("++abs ++ id ++ ":" ++ t ++ ",") <++> local (const ctx) (pprint t') <++> return")"

type BindingList = ([(Maybe String, Term Int)], Term Int)
collectForall :: Term Int -> BindingList
collectForall (Forall id t t') = first ((id,t) :) $ collectForall t'
collectForall t = ([], t)

collectLambda :: Term Int -> BindingList
collectLambda (Lambda id t t') = first ((id,t) :) $ collectLambda t'
collectLambda t = ([], t)

printBindings :: BindingList -> Reader DBContext String
printBindings (bind, body) = print (split bind) (return", " <++> pprint False body)
    where
      split = map (map snd) . groupBy (\(n,(_,t))(n',(_,t'))->(dbShift n t) == dbShift n' t') . zip [0..]
      --printOpen :: [(String, Term Int)] -> Reader DBContext String
      printGroup False l = return (intercalate " " (map fst l) ++ " : ") <++> pprint False (snd $ head l)
      --printClosed :: [(String, Term Int)] -> Reader DBContext String
      printGroup True l = return "(" <++> printGroup False l <++> return ")"
      --print :: [[(Maybe String, Term Int)]] -> Reader DBContext String -> Reader DBContext String
      print l cont = foldr (print' (length l > 1)) cont l
      --printRec :: [(Maybe String, Term Int)] -> Reader DBContext String -> Reader DBContext String
      print' closed l cont = do (ids, cont) <- freshL (map fst l) cont
                                x <- printGroup closed $ zip ids (map snd l)
                                return $ x ++ " " ++ cont
      ----printRec p l = p <++> return " " <++> freshL (map fst l) (printClosed l)

maybeP True p = return "(" <++> p <++> return")"
maybeP False p = p

pprint :: Bool -> Term Int -> Reader DBContext String
pprint paren (Free v) = return "'" <++> return v
pprint paren (Var i) = asks (!! i)
pprint paren t@(Forall _ _ _) = maybeP paren $ return "forall " <++> printBindings (collectForall t)
pprint paren t@(Lambda _ _ _) = maybeP paren $ return "\\" <++> printBindings (collectLambda t)
pprint paren (Sort s) = return $ "%" ++ (show . toInt) s
pprint paren (Apply t t') = maybeP paren $ pprint True t <++> return" " <++> pprint True t'

instance Sort s => Show (Term s) where
    show t = runReader (pprint True $ toIntSort t) []

instance Sort Int where
    sort = id
    toInt = id

instance Sort s => Show (Context s) where
    show = concat . map ((++ "\n") . fmt) . reverse . freeVars
        where fmt (name, Bind t) = name ++ " : " ++ show t
              fmt (name, LetBind t t') = name ++ " = " ++ show t ++ " : " ++ show t'

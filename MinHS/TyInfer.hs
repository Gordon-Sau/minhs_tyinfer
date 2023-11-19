module MinHS.TyInfer where

import MinHS.Bwd
import MinHS.Syntax
import qualified MinHS.Subst as S (Subst, SubstSem, substFlex, substRigid, fromList)
import MinHS.TCMonad

import Control.Monad (foldM)
import Data.List (delete)
import Data.Set (Set, notMember, fromList, difference, member, toList)
import Data.Bifunctor (Bifunctor(..), second)
import MinHS.Subst ((=:))

-- | A monomorphic type injected into a type scheme with no quantified
-- type variables.
mono :: Type -> Scheme
mono t = Forall [] t

rigid :: Id -> Type
rigid = RigidVar

primOpType :: Op -> Scheme
primOpType Gt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = mono $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = mono $ Base Int `Arrow` Base Int
primOpType Fst  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "a"
primOpType Snd  = Forall ["a","b"] $ (RigidVar "a" `Prod` RigidVar "b") `Arrow` RigidVar "b"
primOpType _    = mono $ Base Int `Arrow` (Base Int `Arrow` Base Int)

conType :: Id -> Maybe Scheme
conType "True"  = Just $ mono $ Base Bool
conType "False" = Just $ mono $ Base Bool
conType "()"    = Just $ mono $ Base Unit
conType "Pair"  = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "b" `Arrow` (RigidVar "a" `Prod` RigidVar "b"))
conType "Inl"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "a" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType "Inr"   = Just
                  $ Forall ["a","b"]
                  $ RigidVar "b" `Arrow` (RigidVar "a" `Sum` RigidVar "b")
conType _       = Nothing

freshForall :: [Id] -> TC [(Id,Id)]
freshForall xs = mapM (\x -> (,) <$> pure x <*> freshId) xs

-- | Produce fresh flexible variables for a type scheme
specialise :: Scheme -> TC (Type, Suffix)
specialise (Forall xs t) =
  do ids <- freshForall xs
     return (S.substRigid (S.fromList (map (second FlexVar) ids)) t
            , map (flip (,) HOLE . snd) ids)

-- | Extend a typing context with a collection of flexible declarations
extend :: Gamma -> Suffix -> Gamma
extend g [] = g
extend g ((v,d) : ds) = extend (g :< v := d) ds

infer :: Program -> Either TypeError (Program, Gamma)
infer program = runTC $ inferProgram BEmpty program

unify_flex_flex :: Gamma -> Id -> Id -> TC Gamma
unify_flex_flex (g :< (x:=HOLE)) a b = if x == a then
    return $ g :< (a := (Defn $ flex b)) -- DEFN
  else if x == b then
    return $ g :< (b := (Defn $ flex a)) -- DEFN (sym)
  else do
    g2 <- unify_flex_flex g a b -- SKIP-TY
    return $ g2 :< (x:=HOLE)
unify_flex_flex (g :< (p:=Defn x)) a b = do
  g2 <- unify g
    (S.substFlex (p=:x) $ flex a)
    (S.substFlex (p=:x) $ flex b) -- SUBST
  return $ g2 :< (p:=Defn x)
unify_flex_flex (g :< Mark) a b = do
  g2 <- unify_flex_flex g a b -- SKIP-MARK
  return $ g2 :< Mark
unify_flex_flex (g :< (TermVar x s)) a b = do
  g2 <- unify_flex_flex g a b -- SKIP-TM
  return $ g2 :< (TermVar x s)
unify_flex_flex BEmpty a b = typeError $ UnifyFailed BEmpty (flex a) (flex b)

-- | Perform unification of the given types
unify :: Gamma -> Type -> Type -> TC Gamma
unify g (FlexVar x) (FlexVar y) = if x == y -- REFL
  then return g
  else unify_flex_flex g x y
unify g (FlexVar x) y = inst g [] x y -- INST
unify g y (FlexVar x) = unify g (FlexVar x) y -- INST (sym)
unify g (Arrow a b) (Arrow c d) = do -- ARROW
  g2 <- unify g a c
  unify g2 b d
unify g (Prod a b) (Prod c d) = do -- PROD
  g2 <- unify g a c
  unify g2 b d
unify g (Sum a b) (Sum c d) = do -- SUM
  g2 <- unify g a c
  unify g2 b d
unify g (RigidVar x) (RigidVar y) = if x == y -- Rigid
  then return g
  else typeError $ UnifyFailed g (RigidVar x) (RigidVar y)
unify g (Base x) (Base y) = if x == y -- Base
  then return g
  else typeError $ UnifyFailed g (Base x) (Base y)
unify g t t' = typeError $ UnifyFailed g t t'

appendSuffix :: Gamma -> Suffix -> Gamma
appendSuffix g ((x,d):s) = appendSuffix (g :< (x:=d)) s
appendSuffix g [] = g

-- | Instantiation the type variable a with the type t
inst :: Gamma -> Suffix -> Id -> Type -> TC Gamma
inst (g:<(b:=HOLE)) ds a t = if b == a
  then (if a `member` ffv t
    then typeError $ OccursCheckFailed (g:<(b:=HOLE)) a t
    else return $ appendSuffix g ds :< (b:=Defn t)) -- DEFN
  else if b `member` ffv t
  then inst g ((b,HOLE):ds) a t -- DEPEND
  else do
    g' <- inst g ds a t -- SKIP-TY
    return $ g' :< (b:=HOLE)
inst (g:<(TermVar x s)) ds a t = do
  g' <- inst g ds a t -- SKIP-TM
  return $ g' :< (TermVar x s)
inst (g:<Mark) ds a t = do
  g' <- inst g ds a t -- SKIP-MARK
  return $ g' :< Mark
inst (g:< (b:=Defn s)) ds a t = do -- SUBST
  g' <- unify (appendSuffix g ds) (S.substFlex (b=:s) (flex a)) (S.substFlex (b=:s) t)
  return $ g' :< (b:=Defn s)
inst BEmpty ds a t = typeError $ InstFailed ds a t

inferProgram :: Gamma -> Program -> TC (Program, Gamma)
inferProgram g (SBind x Nothing e) = do
  (s,g') <- inferGen g e
  return (SBind x (Just s) e,g')
inferProgram g (SBind x (Just s) e) = do
  g2 <- inferGenInst g e s
  return (SBind x (Just s) e,g2)

splitMark :: Gamma -> (Gamma,Gamma)
splitMark g = let (g2,delta) = MinHS.Bwd.span (\x -> x /= Mark) g in
  case g2 of
    g3 :< Mark -> (g3,delta)
    _ -> error $ "implementation error: splitMark: Mark expected: " ++ show g

containsBounded :: [Id] -> Gamma -> Bool
containsBounded vs BEmpty = False
containsBounded vs (g:<(_:=Defn t)) = any (flip member $ frv t) vs || containsBounded vs g
containsBounded vs (g:<_) = containsBounded vs g

inferGenInst :: Gamma -> Exp -> Scheme -> TC Gamma
inferGenInst g e (Forall vs t') = do
  (sigma, g2) <- inferGen g e
  (t, suf) <- specialise sigma
  g3 <- unify (extend (g2:<Mark) suf) t t'
  let g4 = fst $ splitMark g3 ;
  if containsBounded vs g4
    then typeError $ UnifyFailed g3 t t'
    else return g4

inferGen :: Gamma -> Exp -> TC (Scheme, Gamma)
inferGen g e = do
  (t,g') <- inferExp (g :< Mark) e
  let (g2,delta) = splitMark g' ;
  let sigma = gen (to_suffix delta) t [] ;
  return (sigma, g2)

to_suffix :: Gamma -> Suffix
to_suffix BEmpty = []
to_suffix (xs :< (x := d)) = (x,d):to_suffix xs
to_suffix xs = error $ "to_suffix: do not expect " ++ show xs

gen :: Suffix -> Type -> [Id] -> Scheme
gen [] t ids = Forall ids t
gen ((x,HOLE):xs) t ids = gen xs (S.substFlex (x =: rigid x) t) $ ids ++ [x]
gen ((x,Defn p):xs) t ids = gen xs (S.substFlex (x =: p) t) ids

find_var_type :: Id -> Gamma -> Maybe Scheme
find_var_type _ BEmpty = Nothing
find_var_type x (bs:<(TermVar y s)) = if x == y then Just s else find_var_type x bs
find_var_type x (bs:<_) = find_var_type x bs

remove :: Eq a => a -> Bwd a -> Bwd a
remove _ BEmpty = BEmpty
remove x (bs:<y) = if x == y then bs else (remove x bs):<y

inferExp :: Gamma -> Exp -> TC (Type, Gamma)
inferExp g (Num _) = return (Base Int,g)
inferExp g (Var x) = case find_var_type x g of
  Just ts -> do
    (t,suf) <- specialise ts
    return (t,extend g suf)
  Nothing -> typeError $ NoSuchVariable x
inferExp g (Con c) = case conType c of
  Just ts -> do
    (t,suf) <- specialise ts
    return (t,extend g suf)
  Nothing -> typeError $ NoSuchConstructor c
inferExp g (Prim op) = do
  (t,suf) <- specialise (primOpType op)
  return (t,extend g suf)
inferExp g (App e1 e2) = do
  (t1,g2) <- inferExp g e1
  (t2,g3) <- inferExp g2 e2
  a <- freshId
  g4 <- unify (g3 :< (a:=HOLE)) t1 (Arrow t2 $ flex a)
  return $ (flex a, g4)
inferExp g (If b e1 e2) = do
  (bt,g2) <- inferExp g b
  g3 <- unify g2 bt (Base Bool)
  (t1,g4) <- inferExp g3 e1
  (t2,g5) <- inferExp g4 e2
  g6 <- unify g5 t1 t2
  return (t1,g6)
-- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  (et,g2) <- inferExp g e
  a <- freshId
  b <- freshId
  g3 <- unify (g2:<(a:=HOLE):<(b:=HOLE)) et (Sum (flex a) (flex b))
  let xbind = TermVar x . mono $ flex a ;
  (t1,g4) <- inferExp (g3:<xbind) e1
  let ybind = TermVar y . mono $ flex b ;
  (t2,g5) <- inferExp (remove xbind g4 :< ybind) e2
  g6 <- unify (remove ybind g5) t1 t2
  return $ (t1,g6)
inferExp _ (Case _ _) = typeError MalformedAlternatives
inferExp g (Recfun (MBind f x e)) = do
  a <- freshId
  b <- freshId
  let xbind = TermVar x . mono $ flex a ;
  let fbind = TermVar f . mono $ flex b ;
  (t,g2) <- inferExp (g:<(a:=HOLE):<(b:=HOLE):<xbind:<fbind) e
  g3 <- unify (remove fbind (remove xbind g2))
    (flex b) (Arrow (flex a) t)
  return (flex b,g3)
inferExp g (Let [] e2) = inferExp g e2
inferExp g (Let (SBind x Nothing e1:sbs) e2) = do
  (s,g2) <- inferGen g e1
  let xbind = TermVar x s ;
  (t,g3) <- inferExp (g2:<xbind) (Let sbs e2)
  return (t,remove xbind g3)
inferExp g (Let (SBind x (Just s) e1:sbs) e2) = do
  g2 <- inferGenInst g e1 s
  let xbind = TermVar x s ;
  (t,g3) <- inferExp (g2:<xbind) (Let sbs e2)
  return (t, remove xbind g3)
inferExp _ _ = error "implement me!"


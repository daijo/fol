{- Resolution.hs -}
{- Charles Chiou -}

module Resolution (askKB) where

import FirstOrderLogic
import NormalForm
import KnowledgeBase

type Subst = [(Variable,Term)]

type SetOfSupport = [Unification]

type Unification = (ImplicativeNormalForm, Subst)

{--
  askKB should be in KnowledgeBase module. However, since resolution is here
  functions are here, it is also placed in this module.
 -}
askKB :: Sentence -> StateMonad (Bool, String)
askKB s = do kbS <- getKB
	     let inf = toINF (Not s)
	     let support = getSetOfSupport inf
             let (tf, proof) = prove [] support kbS
	     return (tf, proof)

{--
  Prove
 -}
prove :: SetOfSupport -> SetOfSupport -> [ImplicativeNormalForm] ->
         (Bool, String)
prove ss1 [] kb = (False, reportSetOfSupport ss1)
prove ss1 (s:ss2) kb =
    let
      (ss', tf) = prove' s kb ss2 ss1
    in
      if tf then
        (True, reportSetOfSupport (ss1 ++ [s] ++ss'))
      else
        prove (ss1 ++ [s]) ss' (fst s:kb)

prove' :: Unification -> [ImplicativeNormalForm] ->
          SetOfSupport -> SetOfSupport -> (SetOfSupport, Bool)
prove' p kb ss1 ss2 =
    let
      res1 = map (\x -> resolution p (x,[])) kb
      res2 = map (\x -> resolution (x,[]) p) kb
      dem1 = map (\e -> demodulate p (e,[])) kb
      dem2 = map (\p' -> demodulate (p',[]) p) kb
      result = getResult (ss1 ++ ss2) (res1 ++ res2 ++ dem1 ++ dem2)
    in
      case result of
        ([], _) -> (ss1, False)
        (l, tf) -> ((ss1 ++ l), tf)

getResult :: SetOfSupport -> [Maybe Unification] ->
           (SetOfSupport, Bool)
getResult _ [] = ([], False)
getResult ss (Nothing:xs) = getResult ss xs
getResult ss ((Just x):xs)  =
    case x of
      ((INF [] []),v) -> ([x], True)
      _ -> if or (map (\(e,_) -> isRenameOf (fst x) e) ss) then
             getResult ss xs
           else
             case getResult ss xs of
               (xs', tf) -> (x:xs', tf)

{--
  Convert the "question" to a set of support.
 -}
getSetOfSupport :: [ImplicativeNormalForm] -> SetOfSupport
getSetOfSupport [] = []
getSetOfSupport (x:xs) = (x, getSubsts x []):getSetOfSupport xs

getSubsts :: ImplicativeNormalForm -> Subst -> Subst
getSubsts (INF lhs rhs) theta =
    let
      theta' = getSubstSentences lhs theta
      theta'' = getSubstSentences rhs theta'
    in
      theta''

getSubstSentences :: [NormalSentence] -> Subst -> Subst
getSubstSentences [] theta = theta
getSubstSentences (x:xs) theta =
    let
      theta' = getSubstSentence x theta
      theta'' = getSubstSentences xs theta'
    in
      theta''

getSubstSentence :: NormalSentence -> Subst -> Subst
getSubstSentence (NFPredicate _ terms) theta = getSubstsTerms terms theta
getSubstSentence (NFNot s) theta = getSubstSentence s theta
getSubstSentence (NFEqual t1 t2) theta =
    let
      theta' = getSubstsTerm t1 theta
      theta'' = getSubstsTerm t2 theta'
    in
      theta''

getSubstsTerms [] theta = theta
getSubstsTerms (x:xs) theta =
    let
      theta' = getSubstsTerm x theta
      theta'' = getSubstsTerms xs theta'
    in
      theta''

getSubstsTerm :: Term -> Subst -> Subst
getSubstsTerm (Function f terms) theta = getSubstsTerms terms theta
getSubstsTerm (Variable v) theta =
    if elem v (map fst theta) then
      theta
    else
      (v, (Variable v)):theta
getSubstsTerm _ theta = theta

isRenameOf :: ImplicativeNormalForm -> ImplicativeNormalForm -> Bool
isRenameOf (INF lhs1 rhs1) (INF lhs2 rhs2) =
    (isRenameOfSentences lhs1 lhs2) && (isRenameOfSentences rhs1 rhs2)

isRenameOfSentences :: [NormalSentence] -> [NormalSentence] -> Bool
isRenameOfSentences xs1 xs2 =
    if length xs1 == length xs2 then
      let
        nsTuples = zip xs1 xs2
      in
        foldl (&&) True (map (\(s1, s2) -> isRenameOfSentence s1 s2) nsTuples)
    else
      False

isRenameOfSentence :: NormalSentence -> NormalSentence -> Bool
isRenameOfSentence (NFPredicate p1 ts1) (NFPredicate p2 ts2) =
    (p1 == p2) && (isRenameOfTerms ts1 ts2)
isRenameOfSentence (NFEqual l1 r1) (NFEqual l2 r2) =
    (isRenameOfTerm l1 l2) && (isRenameOfTerm r1 r2)
isRenameOfSentence _ _ = False

isRenameOfTerm :: Term -> Term -> Bool
isRenameOfTerm (Function f1 t1) (Function f2 t2) =
    (f1 == f2) && (isRenameOfTerms t1 t2)
isRenameOfTerm (Constant c1) (Constant c2) =
    c1 == c2
isRenameOfTerm (Variable v1) (Variable v2) = True
isRenameOfTerm _ _ = False

isRenameOfTerms :: [Term] -> [Term] -> Bool
isRenameOfTerms ts1 ts2 =
    if length ts1 == length ts2 then
      let
        tsTuples = zip ts1 ts2
      in
        foldl (&&) True (map (\(t1, t2) -> isRenameOfTerm t1 t2) tsTuples)
    else
      False

{--
 Resolution:
 -}
resolution :: Unification -> Unification -> Maybe Unification
resolution ((INF lhs1 rhs1), theta1) ((INF lhs2 rhs2), theta2) =
    let
      unifyResult = tryUnify rhs1 lhs2
    in
      case unifyResult of
        Just ((rhs1', theta1'), (lhs2', theta2')) ->
            let
              lhs'' = map (\s -> subst s theta1') lhs1 ++
                      map (\s -> subst s theta2') lhs2'
              rhs'' = map (\s -> subst s theta1') rhs1' ++
                      map (\s -> subst s theta2') rhs2
              theta = updateSubst theta1 theta1' ++
		      updateSubst theta2 theta2'
            in
              Just ((INF lhs'' rhs''), theta)
        Nothing -> Nothing

demodulate :: Unification -> Unification -> Maybe Unification
demodulate (INF [] [NFEqual t1 t2], theta1) (INF lhs2 rhs2, theta2) =
    case findUnify t1 t2 (lhs2 ++ rhs2) of
      Just ((t1', t2'), theta1', theta2') ->
          let
            substLhs2 = map (\x -> subst x theta2') lhs2
            substRhs2 = map (\x -> subst x theta2') rhs2
            lhs = map (\x -> replaceTerm x (t1', t2')) substLhs2
            rhs = map (\x -> replaceTerm x (t1', t2')) substRhs2
            theta = updateSubst theta1 theta1' ++
		    updateSubst theta2 theta2'
          in
            Just (INF lhs rhs, theta)
      Nothing        -> Nothing
demodulate _ _ = Nothing

{-
   Unification: unifies two sentences.
-}
unify :: NormalSentence -> NormalSentence -> Maybe (Subst, Subst)
unify s1 s2 = unify' s1 s2 [] []

unify' :: NormalSentence -> NormalSentence -> Subst -> Subst ->
          Maybe (Subst, Subst)
unify' (NFPredicate p1 ts1) (NFPredicate p2 ts2) theta1 theta2 =
    if p1 == p2 then
      unifyTerms ts1 ts2 theta1 theta2
    else
      Nothing
unify' (NFEqual xt1 xt2) (NFEqual yt1 yt2) theta1 theta2 =
    case unifyTerm xt1 yt1 theta1 theta2 of
      Just (theta1',theta2') -> unifyTerm xt2 yt2 theta1' theta2'
      Nothing -> case unifyTerm xt1 yt2 theta1 theta2 of
                   Just (theta1',theta2') -> unifyTerm xt2 yt1 theta1' theta2'
                   Nothing -> Nothing
unify' _ _ _ _ = Nothing

unifyTerm :: Term -> Term -> Subst -> Subst -> Maybe (Subst, Subst)
unifyTerm (Function f1 ts1) (Function f2 ts2) theta1 theta2 =
    if f1 == f2 then
      unifyTerms ts1 ts2 theta1 theta2
    else
      Nothing
unifyTerm (Constant c1) (Constant c2) theta1 theta2 =
    if c1 == c2 then
      Just (theta1, theta2)
    else
      Nothing
unifyTerm (Variable v1) t2 theta1 theta2 =
    if elem v1 (map fst theta1) then
      let
        t1' = snd (head (filter (\x -> (fst x) == v1) theta1))
      in
        unifyTerm t1' t2 theta1 theta2
    else
      Just ((v1, t2):theta1, theta2)
unifyTerm t1 (Variable v2) theta1 theta2 =
    if elem v2 (map fst theta2) then
      let
        t2' = snd (head (filter (\x -> (fst x) == v2) theta2))
      in
        unifyTerm t1 t2' theta1 theta2
    else
      Just (theta1, (v2,t1):theta2)
unifyTerm _ _ _ _  = Nothing

unifyTerms :: [Term] -> [Term] -> Subst -> Subst -> Maybe (Subst, Subst)
unifyTerms [] [] theta1 theta2 = Just (theta1, theta2)
unifyTerms (t1:ts1) (t2:ts2) theta1 theta2 =
    case (unifyTerm t1 t2 theta1 theta2) of
      Nothing                -> Nothing
      Just (theta1',theta2') -> unifyTerms ts1 ts2 theta1' theta2'
unifyTerms _ _ _ _ = Nothing

tryUnify :: [NormalSentence] -> [NormalSentence] ->
	    Maybe (([NormalSentence], Subst), ([NormalSentence], Subst))
tryUnify lhs rhs = tryUnify' lhs rhs []

tryUnify' :: [NormalSentence] -> [NormalSentence] -> [NormalSentence] -> 
             Maybe (([NormalSentence], Subst), ([NormalSentence], Subst))
tryUnify' [] _ _ = Nothing
tryUnify' (lhs:lhss) rhss lhss' =
    case tryUnify'' lhs rhss [] of
      Nothing -> tryUnify' lhss rhss (lhs:lhss')
      Just (rhss', theta1, theta2) ->
	Just ((lhss' ++ lhss, theta1), (rhss', theta2))

tryUnify'' :: NormalSentence -> [NormalSentence] -> [NormalSentence] -> 
              Maybe ([NormalSentence], Subst, Subst)
tryUnify'' x [] _ = Nothing
tryUnify'' x (rhs:rhss) rhss' =
    case unify x rhs of
      Nothing -> tryUnify'' x rhss (rhs:rhss')
      Just (theta1, theta2) -> Just (rhss' ++ rhss, theta1, theta2)

findUnify :: Term -> Term -> [NormalSentence] ->
	     Maybe ((Term, Term), Subst, Subst)
findUnify tl tr s =
    let
      terms = foldl (++) [] (map getTerms s)
      unifiedTerms' = map (\t -> unifyTerm tl t [] []) terms
      unifiedTerms = filter (\t -> t /= Nothing) unifiedTerms'
    in
     case unifiedTerms of
       [] -> Nothing
       (Just (theta1, theta2)):_ ->
	 Just ((substTerm tl theta1, substTerm tr theta1), theta1, theta2)

getTerms :: NormalSentence -> [Term]
getTerms (NFPredicate p ts) = getTerms' ts
getTerms (NFEqual t1 t2)  = getTerms' [t1] ++ getTerms' [t2]
getTerms _ = []

getTerms' :: [Term] -> [Term]
getTerms' [] = []
getTerms' ((Function f fts):ts) =
    let
      fterms = getTerms' fts ++ getTerms' ts
    in
      (Function f fts):fterms
getTerms' (t:ts) = t:(getTerms' ts)

replaceTerm :: NormalSentence -> (Term, Term) -> NormalSentence
replaceTerm (NFPredicate p ts) (tl', tr') =
    NFPredicate p (map (\t -> replaceTerm' t (tl', tr')) ts)
replaceTerm (NFEqual tr tl) (tl', tr') =
    NFEqual (replaceTerm' tl (tl', tr')) (replaceTerm' tr (tl', tr'))
replaceTerm _ _ = error "error in replaceTerm"

replaceTerm' :: Term -> (Term, Term) -> Term
replaceTerm' t (tl, tr) =
    if t == tl then
      tr
    else
      case t of
        (Function f ts) -> Function f (map (\t -> replaceTerm' t (tl, tr)) ts)
        _  -> t

subst :: NormalSentence -> Subst -> NormalSentence
subst (NFPredicate p ts) theta = NFPredicate p (substTerms ts theta)
subst (NFEqual t1 t2) theta = NFEqual (substTerm t1 theta) (substTerm t2 theta)
subst s _ = s

substTerm :: Term -> Subst -> Term
substTerm (Function f ts) theta = Function f (substTerms ts theta)

substTerm (Variable v) ((sv,st):xs) =
    if v == sv then
      st
    else
      substTerm (Variable v) xs
substTerm t _ = t

substTerms :: [Term] -> Subst -> [Term]
substTerms ts theta = map (\t -> substTerm t theta) ts

updateSubst :: Subst -> Subst -> Subst
updateSubst [] _ = []
updateSubst ((v1,term1):xs) theta =
  case term1 of
    (Variable v') ->
        case filter (\(v,term) -> v == v') theta of
          [] -> (v1,term1):(updateSubst xs theta)
          [(v,term)] -> (v1,term):(updateSubst xs theta)
          _ -> error "error in updateSubst"
    _ -> (v1,term1):(updateSubst xs theta)

reportSetOfSupport :: SetOfSupport -> String
reportSetOfSupport [] = ""
reportSetOfSupport ((inf, theta):xs) = show inf ++ ('\n':reportSetOfSupport xs)

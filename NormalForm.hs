{- NormalForm.hs -}
{- Charles Chiou -}

{- Convert sentences into:
 - Conjunctive Normal Form (CNF) or
 - Implicative Normal Form (INF)
 -}

module NormalForm (ConjunctiveNormalForm(..),
		   ImplicativeNormalForm(..),
		   NormalSentence(..),
		   toCNF, toCNFSentence, showCNFDerivation,
		   toINF, toINFSentence, showINFDerivation) where

import FirstOrderLogic

data ConjunctiveNormalForm = CNF [NormalSentence]
			   deriving Eq

data ImplicativeNormalForm = INF [NormalSentence] [NormalSentence]
			   deriving Eq

data NormalSentence = NFNot NormalSentence
		    | NFPredicate Predicate [Term]
		    | NFEqual Term Term
		    deriving Eq

toCNF :: Sentence -> ConjunctiveNormalForm 
toCNF s = CNF (normalize (toCNFSentence s))

toCNFSentence :: Sentence -> Sentence
toCNFSentence s0 = let
 		     s1 = eliminateImplication s0
		     s2 = moveNotInwards s1
		     s3 = standardizeVariables s2
		     s4 = moveQuantifiersLeft s3
		     s5 = skolemize s4
		     s6 = distributeAndOverOr s5
		   in
		     s6

showCNFDerivation :: Sentence -> String
showCNFDerivation s0 = let
		         s1 = eliminateImplication s0
			 s2 = moveNotInwards s1
			 s3 = standardizeVariables s2
			 s4 = moveQuantifiersLeft s3
			 s5 = skolemize s4
			 s6 = distributeAndOverOr s5
		       in
		         "Input sentence:\t" ++
			 (show s0 ++ "\n") ++
			 "Eliminate implication:\t" ++
			 (show s1 ++ "\n") ++
			 "Move NOT inwards:\t" ++
			 (show s2 ++ "\n") ++
			 "Standardize Variables:\t" ++
			 (show s3 ++ "\n") ++
			 "Move quantifiers left:\t" ++
			 (show s4 ++ "\n") ++
			 "Skolemize variables:\t" ++
			 (show s5 ++ "\n") ++
			 "Distribute AND over OR:\t" ++
			 (show s6 ++ "\n")

toINF :: Sentence -> [ImplicativeNormalForm]
toINF s =
    let
      cnf = toCNFSentence s
      cnfL = collectCnf cnf
    in
      map toINF' cnfL

toINF' :: Sentence -> ImplicativeNormalForm
toINF' s =
    let
      norm = normalize s
      neg' = filter (\ns -> case ns of
		              (NFNot _) -> True
		              otherwise -> False) norm
      neg = map (\ns -> case ns of
		          (NFNot x) -> x
		          otherwise -> error "negative literal on LHS") neg'
      pos = filter (\ns -> case ns of
			     (NFNot _) -> False
		             otherwise -> True) norm
    in
      if neg == [ NFPredicate "True" [] ] then
        INF [] pos
      else
        if pos == [ NFPredicate "False" [] ] then
	  INF neg []
	else
	  INF neg pos

toINFSentence :: Sentence -> Sentence
toINFSentence s0 = let
		     s1 = toCNFSentence s0
		     s2 = disjunctionToImplication s1
		   in
		     s2

showINFDerivation :: Sentence -> String
showINFDerivation s0 = let
		         s1 = toCNFSentence s0
			 s2 = disjunctionToImplication s1
		       in
		         showCNFDerivation s0 ++
			 "Convert disjunctions to implications:\t" ++
			 (show s2 ++ "\n")

{-- 
   Invariants:
   P => Q           becomes       (NOT P) OR Q
   P <=> Q          becomes       ((NOT P) OR Q) AND ((NOT Q) OR P)
 -}
eliminateImplication :: Sentence -> Sentence
eliminateImplication (Connective s1 Imply s2) =
    Connective (Not (eliminateImplication s1)) Or (eliminateImplication s2)
eliminateImplication (Connective s1 Equiv s2) =
    let
      c1 = Connective (Not (eliminateImplication s1)) Or (eliminateImplication s2)
      c2 = Connective (Not (eliminateImplication s2)) Or (eliminateImplication s1)
    in
      Connective c1 And c2

eliminateImplication (Connective s1 c s2) =
    Connective (eliminateImplication s1) c (eliminateImplication s2)
eliminateImplication (Quantifier q vs s) =
    Quantifier q vs (eliminateImplication s)
eliminateImplication (Not s) = Not (eliminateImplication s)
eliminateImplication s = s

{--
   Invariants:
   NOT (P OR Q)      becomes     (NOT P) AND (NOT Q)
   NOT (P AND Q)     becomes     (NOT P) OR (NOT Q)
   NOT (ForAll x P)  becomes     Exists x (NOT P)
   NOT (Exists x P)  becomes     ForAll x (NOT P)
   NOT (NOT P)       becomes     P
 -}
moveNotInwards :: Sentence -> Sentence
moveNotInwards (Connective s1 c s2) =
    Connective (moveNotInwards s1) c (moveNotInwards s2)
moveNotInwards (Quantifier q vs s) = Quantifier q vs (moveNotInwards s)
moveNotInwards (Not (Connective s1 Or s2)) =
    Connective (moveNotInwards (Not s1)) And (moveNotInwards (Not s2))
moveNotInwards (Not (Connective s1 And s2)) =
    Connective (moveNotInwards (Not s1)) Or (moveNotInwards (Not s2))
moveNotInwards (Not (Quantifier ForAll vs s)) =
    Quantifier Exists vs (moveNotInwards (Not s))
moveNotInwards (Not (Quantifier Exists vs s)) =
    Quantifier ForAll vs (moveNotInwards (Not s))
moveNotInwards (Not (Not s)) = moveNotInwards s
moveNotInwards (Not s) = Not (moveNotInwards s)
moveNotInwards s = s

standardizeVariables :: Sentence -> Sentence
standardizeVariables s = s

{--
 
 -}
moveQuantifiersLeft :: Sentence -> Sentence
moveQuantifiersLeft s =
    let
      (s', qs) = collectQuantifiers' s
    in 
      prependQuantifiers' (s', qs)

collectQuantifiers' :: Sentence -> (Sentence, [(Quantifier, [Variable])])
collectQuantifiers' (Not s) =
    let
      (s', qs') = collectQuantifiers' s
    in
      (Not s', qs')
collectQuantifiers' (Quantifier q vs s) =
    let
      (s', qs') = collectQuantifiers' s
    in
      (s', ((q, vs):qs'))
collectQuantifiers' (Connective s1 c s2) =
    let
      (s1', qs1') = collectQuantifiers' s1
      (s2', qs2') = collectQuantifiers' s2
    in
      (Connective s1' c s2', qs1' ++ qs2')
collectQuantifiers' s =  (s, [])

prependQuantifiers' :: (Sentence, [(Quantifier, [Variable])]) -> Sentence
prependQuantifiers' (s, []) = s
prependQuantifiers' (s, ((q, vs):qs)) = Quantifier q vs (prependQuantifiers' (s, qs))


{- 
   Invariants:
   (A AND B) OR C     becomes    (A OR C) AND (B OR C)
   A OR (B AND C)     becomes    (A OR B) AND (B OR C)
  -}
distributeAndOverOr :: Sentence -> Sentence
distributeAndOverOr (Connective (Connective s1 And s2) Or s3) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
      s3' = distributeAndOverOr s3
    in
      distributeAndOverOr (Connective (Connective s1' Or s3') And
			              (Connective s2' Or s3'))
distributeAndOverOr (Connective s1 Or (Connective s2 And s3)) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
      s3' = distributeAndOverOr s3
    in
      distributeAndOverOr (Connective (Connective s1' Or s2') And
			              (Connective s1' Or s3'))
distributeAndOverOr (Connective s1 And s2) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
    in
      (Connective s1' And s2')
distributeAndOverOr (Connective s1 Or s2) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
    in
      (Connective s1' Or s2')
distributeAndOverOr (Quantifier q vs s) =
    Quantifier q vs (distributeAndOverOr s)
distributeAndOverOr s = s

{-
 - Skolemization is tge process of removing existential quantifiers by
 - elimination.
-}
skolemize :: Sentence -> Sentence
skolemize s = skolemize' 1 s [] []

skolemize' :: Int -> Sentence -> [Variable] -> [(Variable, Term)] -> Sentence
skolemize' i (Quantifier ForAll vs s) univ skmap =
    skolemize' i s (univ ++ vs) skmap
skolemize' i (Quantifier Exists vs s) univ skmap =
    skolemize' (i + length vs) s univ (skmap ++ (skolem i vs univ))
skolemize' i (Connective s1 c s2) univ skmap =
    Connective (skolemize' i s1 univ skmap) c (skolemize' i s2 univ skmap)
skolemize' i (Not s) univ skmap =
    Not (skolemize' i s univ skmap)
skolemize' i (Equal t1 t2) univ skmap =
    Equal (substitute t1 skmap) (substitute t2 skmap)
skolemize' i (Predicate p terms) univ skmap =
    Predicate p (map (\x -> substitute x skmap) terms)

skolem :: Int -> [Variable] -> [Variable] -> [(Variable, Term)]
skolem i [] u = []
skolem i (v:vs) u = let
                      skolems =  skolem (i + 1) vs u
		    in
		      if null u then
		        (v, SkolemConstant i):skolems
		      else
		        (v, SkolemFunction i (map Variable u)):skolems

substitute :: Term -> [(Variable, Term)] -> Term
substitute (Variable v) [] = Variable v
substitute var@(Variable v) ((v', t):xs) =
    if v == v' then
      t
    else
      substitute var xs
substitute (Function f terms) xs =
    Function f (map (\x -> substitute x xs) terms)
substitute t _ = t


{--
 - Convert disjunctions to implication:
 -   Collect the negative literals and put them on the left hand side, and
 -   positive literals and put them on the right hand side of the implication.
 -
 - Invariants: The input Sentence is in CNF
 --}

disjunctionToImplication :: Sentence -> Sentence
disjunctionToImplication s =
    let
      cnfL = collectCnf s
      cnfL' = map disjunctionToImplication' cnfL
    in
      foldl (\s1 -> \s2 -> Connective s1 And s2) (head cnfL') (tail cnfL')

disjunctionToImplication' :: Sentence -> Sentence
disjunctionToImplication' s =
    let
      norm = normalize s
      neg' = filter (\ns -> case ns of
		              (NFNot _) -> True
		              otherwise -> False) norm
      neg = map (\ns -> case ns of
		          (NFNot x) -> x
		          otherwise -> error "negative literal on LHS") neg'
      pos = filter (\ns -> case ns of
			     (NFNot _) -> False
		             otherwise -> True) norm
    in
      Connective (denormalize And neg) Imply (denormalize Or pos)

collectCnf :: Sentence -> [Sentence]
collectCnf (Connective s1 And s2) = collectCnf s1 ++ collectCnf s2
collectCnf s = [s]

denormalize :: Connective -> [NormalSentence] -> Sentence
denormalize Imply _ = error ("denormalizing " ++ show Imply)
denormalize Equiv _ = error ("denormalizing " ++ show Equiv)
denormalize And [] = Predicate "True" []
denormalize Or [] = Predicate "False" []
denormalize c (x:[]) = denormalize' x
denormalize c (x:xs) = Connective (denormalize' x) c (denormalize c xs)

denormalize' :: NormalSentence -> Sentence
denormalize' (NFNot s) = denormalize' s
denormalize' (NFPredicate p ts) = Predicate p ts
denormalize' (NFEqual t1 t2) = Equal t1 t2

normalize :: Sentence -> [NormalSentence]
normalize (Connective s1 And s2) = (normalize s1) ++ (normalize s2)
normalize (Connective s1 Or s2) = (normalize s1) ++ (normalize s2)
normalize (Connective s1 c s2) = error ("normailizing " ++ show c)
normalize (Quantifier q _ _) = error ("normalizing " ++ show q)
normalize (Not s) = [NFNot ((head . normalize) s)]
normalize (Predicate p ts) = [NFPredicate p ts]
normalize (Equal t1 t2) = [NFEqual t1 t2]
normalize _ = error "normalizing unknown sentence!"

{--------------------}
{-- Pretty Printing -}
{--------------------}

flattenListString :: String -> String
flattenListString s = filter (\c -> c /= '[' && c /= ']' && c /= '\"') s

connectNormalSentence :: String -> [NormalSentence] -> String
connectNormalSentence s [] = case s of
			       " AND " -> "True"
			       " OR "  -> "False"
connectNormalSentence s (x:[]) = show x
connectNormalSentence s (x:xs) = show x ++ s ++ connectNormalSentence s xs

instance Show ConjunctiveNormalForm where
    show (CNF xs) = connectNormalSentence "\n" xs

instance Show ImplicativeNormalForm where
    show (INF ls rs) = connectNormalSentence " AND " ls ++ " => " ++
		       connectNormalSentence " OR " rs

instance Show NormalSentence where
    show (NFNot s) = "NOT " ++ "(" ++ show s ++ ")"
    show (NFPredicate p []) = p
    show (NFPredicate p ts) = p ++ "(" ++ (flattenListString (show ts)) ++ ")"
    show (NFEqual t1 t2) = show t1 ++ "=" ++ show t2
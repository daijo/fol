{- FirstOrderLogic.hs -}
{-
  The syntax of first order logic in BNF is:
  
  Sentence -> AtomicSentence
           |  Sentence Connective
	   |  Quantifier Variable, ... Sentence
	   |  NOT Sentence
	   | (Sentence)
	   
  AtomicSentence -> Predicate(Term, ...)
                 |  Term = Term

  Term -> Function (Term)
       |  Constant
       |  Variable

  Connective -> =>
             |  <=>
             |  AND
	     |  OR

  Quantifier -> ForAll
             |  Exists

  Constant -> A | X | John | ...
  
  Variable -> a | x | s | ...

  Predicate -> Before | HasColor | Raining | ...

  Function -> Mother | LeftLegOf | ...

  [Source: S. Russel, P. Norvig, "Artificial Intelligence: A modern Approach",
           p187]
  -}

module FirstOrderLogic (Sentence(..),
			Term(..),
			Connective(..),
			Quantifier(..),
			Constant, Variable, Predicate, Function,
			parseFOL) where

import ParseLib

data Sentence = Connective Sentence Connective Sentence
	      | Quantifier Quantifier [Variable] Sentence
	      | Not Sentence
	      | Predicate Predicate [Term]
	      | Equal Term Term
	      deriving Eq

data Term = Function Function [Term]
	  | Constant Constant
	  | Variable Variable
	  | SkolemFunction Int [Term]
	  | SkolemConstant Int
	  deriving Eq

data Connective = Imply
		| Equiv
		| And
		| Or
		deriving Eq

data Quantifier = ForAll
		| Exists
		deriving Eq

type Constant = String

type Variable = String

type Predicate = String

type Function = String

{-------------------------------------------------------------------}
{-- A monadic combinator parser for sentences in first-order logic -}
{-------------------------------------------------------------------}

parseFOL :: String -> Maybe Sentence
parseFOL s =
    case (papply sentence s) of
      [] -> Nothing
      xs -> case ((snd . head) xs) of
	      [] -> Just ((fst . head) xs)
	      _ -> Nothing

-- Sentence parsers

sentence :: Parser Sentence
sentence = sQuant +++ sConn +++ sNot +++ sAtomic

sAtomic :: Parser Sentence
sAtomic = sEqual +++ sPred +++ sBracket

sBracket :: Parser Sentence
sBracket = bracket (symbol "(") sentence (symbol ")")

sPred :: Parser Sentence
sPred = do p <- predicate
	   ts <- bracket (symbol "(") terms (symbol ")") +++ (return [])
	   return (Predicate p ts)

sEqual :: Parser Sentence
sEqual = do t1 <- term
	    symbol "="
	    t2 <- term
	    return (Equal t1 t2)

sConn :: Parser Sentence
sConn = let
	  s1 = sAtomic +++ sNot
	  s2 = sAnd +++ s1
	  s3 = sOr +++ s2
	  s4 = sImply +++ s3
	  sAnd = s1 `chainl1` cAnd
	  sOr = s2 `chainl1` cOr
	  sImply = s3 `chainl1` cImply
	  sEquiv = s4 `chainl1` cEquiv
	in
	  sEquiv +++ sImply +++ sOr +++ sAnd

cImply :: Parser (Sentence -> Sentence -> Sentence)
cImply = do symbol "=>"
	    return (\s1 -> \s2 -> Connective s1 Imply s2)

cEquiv :: Parser (Sentence -> Sentence -> Sentence)
cEquiv = do symbol "<=>"
	    return (\s1 -> \s2 -> Connective s1 Equiv s2)

cAnd :: Parser (Sentence -> Sentence -> Sentence)
cAnd = do symbol "AND" +++ symbol "And" +++ symbol "and"
	  return (\s1 -> \s2 -> Connective s1 And s2)

cOr :: Parser (Sentence -> Sentence -> Sentence)
cOr = do symbol "OR" +++ symbol "Or" +++ symbol "or"
	 return (\s1 -> \s2 -> Connective s1 Or s2)

sQuant :: Parser Sentence
sQuant = do q <- quantifier
	    vs <- variables
	    s <- sentence
	    return (Quantifier q vs s)

sNot :: Parser Sentence
sNot = do symbol "NOT" +++ symbol "Not" +++ symbol "not"
	  s <- sAtomic
	  return (Not s)

-- Term parsers

term :: Parser Term
term = tFunc +++ tConst +++ tVar

terms :: Parser [Term]
terms = (token term) `sepby1` char ','

tFunc :: Parser Term
tFunc = do f <- function
	   ts <- bracket (symbol "(") terms (symbol ")")
	   return (Function f ts)

tConst :: Parser Term
tConst = do c <- constant
	    return (Constant c)

tVar :: Parser Term
tVar = do v <- variable
	  return (Variable v)

-- Connective parser

connective :: Parser Connective
connective = do s <- symbol "=>" +++ symbol "<=>" +++
		     symbol "AND" +++ symbol "And" +++ symbol "and" +++
		     symbol "OR" +++ symbol "Or" +++ symbol "or"
		case s of
		  "=>"  -> return Imply
		  "<=>" -> return Equiv
		  "AND" -> return And
		  "And" -> return And
		  "and" -> return And
		  "OR"  -> return Or
		  "Or"  -> return Or
		  "or"  -> return Or
		  _     -> mzero

-- Quatifier parser

quantifier :: Parser Quantifier
quantifier = do s <- symbol "FORALL" +++ symbol "ForAll" +++ symbol "forall" +++
		     symbol "EXISTS" +++ symbol "Exists" +++ symbol "exists"
		case s of
		  "FORALL" -> return ForAll
		  "ForAll" -> return ForAll
		  "forall" -> return ForAll
		  "EXISTS" -> return Exists
		  "Exists" -> return Exists
		  "exists" -> return Exists
		  _        -> mzero

-- Lexers

keywords :: [String]
keywords = [ "TRUE", "True", "true",
	     "FALSE", "False", "false",
	     "NOT", "Not", "not",
	     "AND", "And", "and",
	     "OR", "Or", "or",
	     "FORALL", "ForAll", "forall",
	     "EXISTS", "Exists", "exists" ]

variable :: Parser String
variable = identifier keywords

variables :: Parser [String]
variables = (token variable) `sepby1` char ','

constant, predicate, function :: Parser String
constant = capitalized
predicate = capitalized
function = capitalized

capitalized :: Parser String
capitalized = token (do x <- upper
		        xs <- many alphanum
		        (if not (elem (x:xs) keywords) then
		           return (x:xs)
		         else
                           mzero))

{---------------------}
{-- Pretty Printing --}
{---------------------}

flattenListString :: String -> String
flattenListString s = filter (\c -> c /= '[' && c /= ']' && c /= '\"') s

instance Show Sentence where
    show (Connective s1 c s2) = "(" ++ show s1 ++ show c ++ show s2 ++ ")"
    show (Quantifier q [] s) = show q ++ " " ++ show s
    show (Quantifier q vs s) = show q ++ " " ++ (flattenListString (show vs)) ++
			       " " ++ show s
    show (Not s) = "NOT " ++ "(" ++ show s ++ ")"
    show (Predicate p []) = p
    show (Predicate p ts) = p ++ "(" ++ (flattenListString (show ts)) ++ ")"
    show (Equal t1 t2) = show t1 ++ "=" ++ show t2

instance Show Term where
    show (Function f ts) = f ++ "(" ++ (flattenListString (show ts)) ++ ")"
    show (Constant c) = c
    show (Variable v) = v
    show (SkolemFunction i ts) = "SKOLEM_FUNCTION_" ++ show i ++ "(" ++
				 (flattenListString (show ts)) ++ ")"
    show (SkolemConstant i) = "SKOLEM_CONSTANT_" ++ show i

instance Show Connective where
    show (Imply) = " => "
    show (Equiv) = " <=> "
    show (And)   = " AND "
    show (Or)    = " OR "

instance Show Quantifier where
    show (ForAll) = "ForAll"
    show (Exists) = "Exists"
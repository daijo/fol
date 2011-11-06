{- KnowledgeBase.hs -}
{- Charles Chiou -}

module KnowledgeBase (State(..), StateMonad(..),
		      readState, updateState, runState,
		      zeroKB, emptyKB,
		      getKB, loadKB, unloadKB,
		      tellKB, deleteKB, showKB) where

import Monad
import FirstOrderLogic
import NormalForm

data StateMonad a = StateMonad (State -> (a, State))

type State = ([(ImplicativeNormalForm, Int)], SkolemCount, [FolModule])

type SkolemCount = Int

type FolModule = (String, Int)

instance Monad StateMonad where
  StateMonad c1 >>= fc2 =  StateMonad (\s0 -> let (r,s1) = c1 s0 
                                                  StateMonad c2 = fc2 r
				              in
                                              c2 s1)
  return k =  StateMonad (\s -> (k, s))

readState :: StateMonad State
readState =  StateMonad (\s -> (s, s))

updateState :: (State -> State) -> StateMonad ()
updateState f =  StateMonad (\s -> ((), f s)) 

runState :: State -> StateMonad a -> (a, State)
runState s0 (StateMonad c)= c s0

{- Operations on the knowledge base -}

zeroKB :: State
zeroKB = ([], 0, [("user", 0)])

emptyKB :: StateMonad ()
emptyKB = updateState (\s -> zeroKB)

getKB :: StateMonad [ImplicativeNormalForm]
getKB = do (kbS, _, _) <- readState
	   return (map fst kbS)

tellKB :: Sentence -> Int -> StateMonad String
tellKB s i = do (kbS, c, _) <- readState
		(inf, sc) <-  assignSkolemL (toINF s) i
	        updateState (\(kbS', c', m') -> (kbS' ++ inf, c' + sc, m'))
  	        return (show (map fst inf))

assignSkolemL :: [ImplicativeNormalForm] -> Int ->
		 StateMonad ([(ImplicativeNormalForm, Int)], Int)
assignSkolemL [] i = return ([], 0)
assignSkolemL (x:xs) i = do (x', n1) <- assignSkolem x i
			    (xs', n2) <- assignSkolemL xs i
			    return (x' ++ xs', max n1 n2)

assignSkolem :: ImplicativeNormalForm -> Int ->
		StateMonad ([(ImplicativeNormalForm, Int)], Int)
assignSkolem (INF lhs rhs) i =
    do (lhs', n1) <- assignSkolem' lhs
       (rhs', n2) <- assignSkolem' rhs
       let inf = if n2 > 0 then
	           map (\x -> (x, i)) (splitSkolem (INF lhs' rhs'))
		 else
		   [((INF lhs' rhs'), i)]
       return (inf, max n1 n2)

assignSkolem' :: [NormalSentence] -> StateMonad ([NormalSentence], Int)
assignSkolem' [] = return ([], 0)
assignSkolem' (x:xs) = do (x', n1) <- assignSkolem'' x
			  (xs', n2) <- assignSkolem' xs
			  return ((x':xs'), max n1 n2)

assignSkolem'' :: NormalSentence -> StateMonad (NormalSentence, Int)
assignSkolem'' (NFNot s) = do (s', n) <- assignSkolem'' s
			      return (NFNot s', n)
assignSkolem'' (NFPredicate p ts) = do (ts', n) <- skSubstituteL ts
				       return (NFPredicate p ts', n)
assignSkolem'' (NFEqual t1 t2) = do (t1', n1) <- skSubstitute t1
				    (t2', n2) <- skSubstitute t2
				    return (NFEqual t1' t2', max n1 n2)

skSubstituteL :: [Term] -> StateMonad ([Term], Int)
skSubstituteL [] = return ([], 0)
skSubstituteL (t:ts) = do (t', n1) <- skSubstitute t
			  (ts', n2) <- skSubstituteL ts
			  return (t':ts', max n1 n2)

skSubstitute :: Term -> StateMonad (Term, Int)
skSubstitute t = case t of
	           (Function f ts) ->
		       do (ts', n) <- skSubstituteL ts
			  return (Function f ts', n)
		   (SkolemFunction n ts) ->
		       do (ts', n') <- skSubstituteL ts
			  (_, c, _) <- readState
			  return ((Function ("?SKF_" ++ show (n + c)) ts'),
				   max n n')
		   (SkolemConstant n) ->
		       do (_, c, _) <- readState
			  return (Constant ("?SKC_" ++ show (n + c)), n)
		   otherwise -> return (t, 0)

splitSkolem :: ImplicativeNormalForm -> [ImplicativeNormalForm]
splitSkolem (INF lhs []) = [INF lhs []]
splitSkolem (INF lhs (x:[])) = [INF lhs [x]]
splitSkolem (INF lhs (x:xs)) = (INF lhs [x]):(splitSkolem (INF lhs xs))

{- This is very ugly -}
loadKB :: String -> StateMonad String
loadKB f = do unloadKB f
	      --fin <- readFile f
	      let fin = myReadFile f
	      (_, _, m) <- readState
	      let idx = (case m of
			   [] -> 1
			   _  -> snd (last m) + 1)
	      (n, msg) <- loadKB' (lines fin) idx
	      let newmod = (if n > 0 then
			      [(f, idx)]
			    else
			      [])
              updateState (\(kbS', c', m') -> (kbS', c', m' ++ newmod))
	      return (if n > 0 then
		        "Loaded " ++ show n ++ " entries from " ++ f ++
			":\n" ++ msg
		      else
		        "\nNo entries loaded from " ++ f)

loadKB' :: [String] -> Int -> StateMonad (Int, String)
loadKB' [] _ = return (0, "")
loadKB' (x:xs) i =
    let
      sentence = parseFOL x
    in
      do (case sentence of
	  Just sentence' -> do tellKB sentence' i
	                       (n', msg') <- loadKB' xs i
	                       return (1 + n', show sentence' ++ "\n" ++ msg')
	  Nothing -> do (n', msg') <- loadKB' xs i
			return (n', "parse error: " ++ x ++ "\n" ++ msg'))

unloadKB :: String -> StateMonad String
unloadKB f =
    do (_, _, m) <- readState
       (case lookup f m of 
	  Nothing -> return ("Module " ++ f ++ " is not loaded!")
	  Just idx -> do updateState (\(kbS', c', m') ->
		                       (filter (\(inf, mi) -> mi /= idx) kbS',
	                                c',
	                                filter (\(mn, mi) -> mi /= idx) m'))
			 return ("Module " ++ f ++ " unloaded"))

deleteKB :: Int -> StateMonad String
deleteKB i = do (kbS, c, _) <- readState
		updateState (\(kbS', c', m') -> (deleteElement i kbS', c', m'))
		(kbS', c', _) <- readState
		return (if (length kbS') /= (length kbS) then
			  "Deleted"
			else
			  "Failed to delete")
	     
deleteElement :: Int -> [a] -> [a]
deleteElement i l
    | i <= 0    = l
    | otherwise = let
		    (p1, p2) = splitAt (i - 1) l
		  in
		    p1 ++ (case p2 of
			       [] -> []
			       otherwise -> tail p2)

showKB :: StateMonad String
showKB = do (kbS, c, m) <- readState
	    return (reportKB 1 (kbS, c, m))

reportKB :: Int -> State -> String
reportKB i ([], _, _) = "Nothing in Knowledge Base\n"
reportKB i ((x:[]), c, m) = show i ++ ") " ++ reportKB' (snd x) m ++ "\t" ++
			    show (fst x) ++ "\n"
reportKB i ((x:xs), c, m) = show i ++ ") " ++ reportKB' (snd x) m ++  "\t" ++
			    show (fst x) ++ "\n" ++
			    reportKB (i + 1) (xs, c, m)

reportKB' :: Int -> [FolModule] -> String
reportKB' 0 m = "[USER]"
reportKB' i m =
    case lookup i (map (\(a, b) -> (b, a)) m) of
      Just x -> "[MOD:" ++ x ++ "]"
      Nothing -> "ERROR"

{-
 Some IO hack here...
 -}

myReadFile :: String -> String
myReadFile f = case hugsIORun (readFile f) of
	         Right s -> s
		 Left _ -> ""

hugsPutStr :: String -> IO ()
hugsPutStr  = putStr

hugsIORun  :: IO a -> Either Int a
hugsIORun m = performIO (runAndShowError m)
 where
  performIO       :: IO a -> Either Int a
  performIO (IO m) = case m Hugs_Error Hugs_Return of
                     Hugs_Return a   -> Right a
                     Hugs_ExitWith e -> Left  e
                     _               -> Left  1

  runAndShowError :: IO a -> IO a
  runAndShowError m =
    m `catch` \err -> do
        putChar '\n'
        putStr (ioeGetErrorString err)
        primExitWith 1 -- alternatively: (IO (\f s -> Hugs_SuspendThread))

primitive ioeGetErrorString "primShowIOError" :: IOError -> String

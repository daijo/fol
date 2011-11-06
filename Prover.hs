{- Prover.hs -}
{- Charles Chiou -}

import ParseLib
import Interact
import FirstOrderLogic
import NormalForm
import KnowledgeBase
import Resolution

data Cmd = TellCmd String
	 | AskCmd String
	 | DeleteCmd Int
	 | LoadCmd String
	 | UnloadCmd String
	 | ResetCmd
	 | ShowCmd
	 | QuitCmd
	 | HelpCmd
	 | DebugCmd String
	 | ErrorCmd

main :: IO ()
main = do putStr "Welcome to First Order Logic Prover!\n\n"
	  is <- getContents
	  putStr (loop zeroKB is)

loop :: State -> String -> String
loop s = readLine "Prover> " ((processCmd s) . parseCmd)

processCmd :: State -> Cmd -> String -> String
processCmd s (TellCmd c) = tellCmd s c
processCmd s (AskCmd c) = askCmd s c
processCmd s (DeleteCmd i) = deleteCmd s i
processCmd s (LoadCmd f) = loadCmd s f
processCmd s (UnloadCmd f) = unloadCmd s f
processCmd s ResetCmd = resetCmd s
processCmd s ShowCmd = showCmd s
processCmd s QuitCmd = writeStr "Bye!\n" end
processCmd s HelpCmd = writeStr helpMessage (loop s)
processCmd s (DebugCmd c) = debugCmd s c
processCmd s ErrorCmd = writeStr "Huh? (type 'help' for commands)\n" (loop s)

tellCmd :: State -> String -> Interact
tellCmd s c =
    let
      c' = parseFOL c
    in
      case c' of
        Nothing -> writeStr "Syntax error!\n" (loop s)
	Just sentence -> let
			   (result, s') = runState s (tellKB sentence 0)
			 in
			   writeStr (result ++ "\n") (loop s')


askCmd :: State -> String -> Interact
askCmd s c =
    let
     c' = parseFOL c
    in
      case c' of
        Nothing -> writeStr "Syntax error!\n" (loop s)
	Just sentence -> let
			   ((tf, proof), s') =
			       runState s (askKB sentence)
			 in
			   case tf of
			     True ->  writeStr ("Result: *Yes*\n")
				      (askSeePoof s' proof)
			     False -> writeStr ("Result: *No*\n")
				      (askSeePoof s' proof)

askSeePoof :: State -> String -> Interact
askSeePoof s proof =
    writeStr "Would you like to see the proof (y/n)?"
             (readChar end
              (\c -> if c == 'y' then
	               writeStr ("\nProof:\n" ++ proof) (loop s)
                     else
	               writeStr "\n" (loop s)))

deleteCmd :: State -> Int -> Interact
deleteCmd s i =
    let
      (msg, s') = runState s (deleteKB i)
    in
      writeStr (msg ++ "\n") (loop s')

loadCmd :: State -> String -> Interact
loadCmd s f =
    let
      (msg, s') = runState s (loadKB f)
    in
      writeStr (msg ++ "\n") (loop s')

unloadCmd :: State -> String -> Interact
unloadCmd s f =
    let
      (msg, s') = runState s (unloadKB f)
    in
      writeStr (msg ++ "\n") (loop s')

resetCmd :: State -> Interact
resetCmd s =
    let
      (_, s') = runState s emptyKB
    in
      writeStr "Knowledge base resetted.\n" (loop s')

showCmd :: State -> Interact
showCmd s =
    let
      (report, s') = runState s showKB
    in
      writeStr report (loop s')

debugCmd :: State -> String -> Interact
debugCmd s c =
    let
     c' = parseFOL c
    in
      case c' of
        Nothing -> writeStr "Syntax error!\n" (loop s)
	Just sentence -> writeStr (showINFDerivation sentence) (loop s)

helpMessage :: String
helpMessage =
    "|==================================================================|\n" ++
    "|                  H        E        L        P                    |\n" ++
    "|==================================================================|\n" ++
    "| Writing sentences in First-Order-Logic:                          |\n" ++
    "|   1) The keywords are: NOT, AND, OR, =>, <=>, =, ForAll, Exists  |\n" ++
    "|   2) Variables must begin with a lower case letter.              |\n" ++
    "|   3) Predicates, functions, constants, must begin with an upper  |\n" ++
    "|      case letter.                                                |\n" ++
    "|   4) Predicates and functions are followed by parentheses ().    |\n" ++
    "|__________________________________________________________________|\n" ++
    "|                                                                  |\n" ++
    "| The valid commands are:                                          |\n" ++
    "|   Tell <sentence>  - Inserts a sentence into the KB.             |\n" ++
    "|   Ask <sentence>   - Proves a sentence (True, False).            |\n" ++
    "|   Delete [index]   - Deletes an entry from the KB.               |\n" ++
    "|   Load <file>      - Loads a file as a module into the KB.       |\n" ++
    "|   Unload <file>    - Unloads a previously loaded module.         |\n" ++
    "|   Reset            - Resets the KB to empty.                     |\n" ++
    "|   Show             - Displays the contents of the KB             |\n" ++
    "|   Quit             - Quits this program.                         |\n" ++
    "|   Help             - Displays this message.                      |\n" ++
    "|==================================================================|\n"


-- Command parser

parseCmd :: String -> Cmd
parseCmd s = case (papply cmd s) of
	        [] -> ErrorCmd
	        xs -> case ((snd . head) xs) of
			     [] -> ((fst . head) xs)
			     _ -> ErrorCmd

cmd :: Parser Cmd
cmd = ctell +++ cask +++ cdelete +++ cload +++ cunload +++
      creset +++ cshow +++ cquit +++ chelp +++ cdebug

ctell :: Parser Cmd
ctell = do symbol "TELL" +++ symbol "Tell" +++ symbol "tell"
	   s <- everything
	   return (TellCmd s)

cask :: Parser Cmd
cask = do symbol "ASK" +++ symbol "Ask" +++ symbol "ask"
	  s <- everything
	  return (AskCmd s)

cdelete :: Parser Cmd
cdelete = do symbol "DELETE" +++ symbol "Delete" +++ symbol "delete"
	     i <- nat
	     return (DeleteCmd i)

cload :: Parser Cmd
cload = do symbol "LOAD" +++ symbol "Load" +++ symbol "load"
	   file <- fname
	   return (LoadCmd file)

cunload :: Parser Cmd
cunload = do symbol "UNLOAD" +++ symbol "Unload" +++ symbol "unload"
	     file <- fname
	     return (UnloadCmd file)

creset :: Parser Cmd
creset = do symbol "RESET" +++ symbol "Reset" +++ symbol "reset"
	    return (ResetCmd)

cshow :: Parser Cmd
cshow = do symbol "SHOW" +++ symbol "Show" +++ symbol "show"
	   return (ShowCmd)

cquit :: Parser Cmd
cquit = do symbol "QUIT"  +++ symbol "Quit" +++ symbol "quit"
	   return (QuitCmd)

chelp :: Parser Cmd
chelp = do symbol "HELP"  +++ symbol "Help" +++ symbol "help"
	   return (HelpCmd)

cdebug :: Parser Cmd
cdebug = do symbol "DEBUG"  +++ symbol "Debug" +++ symbol "debug"
	    s <- everything
	    return (DebugCmd s)

everything :: Parser String
everything = token (do s <- many item
		       return s)

fname :: Parser String
fname = token (do s <- many (sat isAlphaNum +++ char '.')
	          return s)
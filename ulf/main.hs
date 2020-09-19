{-# Language BlockArguments #-}

import Control.Monad (join)
import Options.Applicative

type Command = ParserInfo (IO ())

runCheck :: [FilePath] -> Bool -> IO ()
runCheck _ _ = putStrLn "checking"

runServer :: IO ()
runServer = putStrLn "serving"

checkCommand :: Command
checkCommand = info (helper <*> (runCheck <$> many file <*> elaborate))
   $ fullDesc
  <> progDesc "Type check a program"
  <> header "ergo check"
  where 
     file = strArgument
        $ metavar "FILES..." 
       <> action "file"
       <> help (unlines 
          [ "Input source files" 
          ])
     elaborate = switch 
        $ long "elaborate" 
       <> help "Print elaborated syntax after type checking"

serverCommand :: Command
serverCommand = info (pure runServer)
   $ fullDesc
  <> progDesc "Start the language server"
  <> header "ergo server"

commands :: Parser (IO ())
commands = subparser 
   $ command "check" checkCommand
  <> command "server" serverCommand

optionsParser :: Command
optionsParser = info (helper <*> commands)
   $ fullDesc
  <> progDesc "ergo compiler"
  <> header "ergo"
  
main :: IO ()
main = join $ execParser optionsParser
  

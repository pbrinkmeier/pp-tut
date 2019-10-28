module Hangman where

main =
  runConsoleGame
  (showHangman guessWord)
    (updateHangman guessWord)
    initHangman
  where
    guessWord = "Haskell"

runConsoleGame :: (s -> String) -> (String -> s -> s) -> s -> IO ()
runConsoleGame showGame updateGame gameState = do
  putStrLn (showGame gameState)
  inputLine <- getLine
  runConsoleGame showGame updateGame (updateGame inputLine gameState)

-- Tut-Code: --

showHangman word guesses = ""

initHangman = []

updateHangman word inputLine guesses = guesses

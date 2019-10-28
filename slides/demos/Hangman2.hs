module Hangman2 where

import Data.List
import Data.Maybe

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

showHangman word guesses =
  intercalate "\n" (catMaybes [ wordDisplay, guessDisplay, messageDisplay ])
  where
    wordDisplay = Just
      (intersperse ' ' [ if c `elem` guesses then c else '_' | c <- word ])
    guessDisplay = Just
      (intersperse ' ' guesses)
    messageDisplay =
      if all (\c -> c `elem` guesses) word then
        Just "Richtig geraten!"
      else
        Nothing

initHangman = []

updateHangman word inputLine guesses
  | length inputLine == 1             = (head inputLine : guesses)
  | otherwise                         = guesses

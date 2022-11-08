module Hangman where

main :: IO ()
main = runConsoleGame (showHangman word) updateHangman []
    where word = "haskell"

runConsoleGame
    :: (s -> String)
    -> (String -> s -> s)
    -> s
    -> IO ()
runConsoleGame showGame updateGame state = do
    putStr $ showGame state
    input <- getLine
    runConsoleGame showGame updateGame (updateGame input state)

-- TODO: implement this
showHangman word guesses = unlines [ " O ", "/|\\", "/ \\" ]

-- TODO: implement this
updateHangman inputLine guesses = guesses

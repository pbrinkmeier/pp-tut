module Hangman where

import Control.Monad (unless)
import System.Random

main :: IO ()
main = do
    runConsoleGame showHangman updateHangman shouldStop (Hangman word [])
    where word = "laziness"

runConsoleGame
    :: (s -> String)      -- ^ A function that displays game state for the user.
    -> (String -> s -> s) -- ^ How to update game state given an input line.
    -> (s -> Bool)        -- ^ A predicate for states that stop the game loop.
    -> s                  -- ^ Initial game state.
    -> IO ()
runConsoleGame showGame updateGame isFinal = loop
    where
        loop state = do
            putStr $ showGame state
            unless (isFinal state) $ do
                input <- getLine
                loop (updateGame input state)

data Hangman = Hangman
    String -- ^ Secret word.
    [Char] -- ^ List of guesses.

showHangman (Hangman word guesses)
    -- Not all characters of the secret word have been guessed.
    | any (`notElem` guesses) word = unlines
        [ unlines $ take (length wrongs) parts
        , "Wrong characters: " ++ show wrongs
        , [ if c `elem` guesses then c else '.' | c <- word ]
        , replicate 10 '#'
        ]
    -- All characters have been guessed.
    | otherwise = "The word was '" ++ word ++ "'. You win! 🎉\n"
    where
        wrongs = filter (`notElem` word) guesses
        parts =
            [ "+---+"
            , "|   |"
            , "|   O "
            , "|  /|\\"
            , "|  / \\"
            , "|"
            , "#######"
            , "You died 💀" ]

-- TODO: implement this
updateHangman [guess] (Hangman word guesses)
    | guess `notElem` guesses = Hangman word (guess : guesses)
updateHangman _ s =
    s

shouldStop (Hangman word guesses) =
    -- The game should stop when either
    -- i.  The user gave 8 wrong guesses.
    -- ii. The whole secret word was guessed.
    length wrongs >= 8 || all (`elem` guesses) word
    where wrongs = filter (`notElem` word) guesses

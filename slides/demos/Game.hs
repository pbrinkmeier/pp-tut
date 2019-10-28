module Game where

main = gameLoop initialState

gameLoop state = do
  printBoard state
  userInput <- getLine
  gameLoop (update userInput state)

printBoard :: (Int, Int) -> IO ()
printBoard state = do
  printLine 3 state
  printLine 2 state
  printLine 1 state
  printLine 0 state
  printLine (-1) state
  printLine (-2) state
  printLine (-3) state

printLine line playerPos =
  putStrLn [ if (col, line) == playerPos then '#' else '.' | col <- [-3 .. 3] ]

initialState = (0, 0)

update "west" (x, y) = (x - 1, y)
update "east" (x, y) = (x + 1, y)
update "north" (x, y) = (x, y + 1)
update "south" (x, y) = (x, y - 1)
update _ state = state

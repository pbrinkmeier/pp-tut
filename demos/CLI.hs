module CLI where

runConsoleGame ::
  (s -> String) ->
  (String -> s -> s) ->
  s ->
  IO ()

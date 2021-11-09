module MiMa where

data MimaInst
  = LDC Int | LDV Int | STV Int
  | ADD Int | AND Int | OR Int
  | EQL Int | JMP Int | JMN Int
  | HALT | NOT | RAR

-- Alternatively:
data MimaInst' =
  Nullary MimaNullary | Unary MimaUnary Int
data MimaUnary = LDC' | LDV' | STV' | ADD' -- ...
data MimaNullary = HALT' | NOT' | RAR'

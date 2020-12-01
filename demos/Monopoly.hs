module Monopoly where

data MonopolyCard
  = Street String Rent Int Color
  | Station String
  | Utility String

data Rent = Rent Int Int Int Int Int

data Color
  = Brown | LightBlue | Pink  | Orange
  | Red   | Yellow    | Green | Blue

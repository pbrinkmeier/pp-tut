module Mappable where

class Mappable m where
  mmap :: (a -> b) -> m a -> m b

module Queue where

import List

data Queue a = Queue (List a) (List a)

pushHead x (Queue front back) =
  Queue (Cons x front) back
pushLast x (Queue front back) =
  Queue front (Cons x back)

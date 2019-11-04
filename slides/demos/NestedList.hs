module NestedList where

type Nested a = [[[[[[[[[[[a]]]]]]]]]]]

a1 = [[[[[[[[[[[0]]]]]]]]]]] -- :: Nested a
a2 = [[[[[[[[[[[ ]]]]]]]]]]]    :: Nested a
a3 =  [[[[[[[[[[ ]]]]]]]]]]     :: Nested a
a4 =     [[[[[[[ ]]]]]]]        :: Nested a
a5 =           [ ]              :: Nested a
a6 =           []               :: Nested a

{-@ LIQUID "--reflection" @-}

module Ship where

import Prelude hiding (abs)

{-@
data Ship = Ship {
  capacity :: Int,
  x        :: Int,
  y        :: Int
}
@-}
data Ship = Ship {
  capacity :: Int,
  x        :: Int,
  y        :: Int
}
{-# ANN Ship ([
  ("capacity", (0, 100)),
  ("x", (0, 500)),
  ("y", (0, 500))
  ] :: [(String, (Int, Int))]) #-}

{-@ reflect abs @-}
abs :: Int -> Int
abs i | i < 0 = -1 * i
abs i         = i

{-@ reflect query @-}
query :: Ship -> Bool
query secret = (capacity secret) > limit && (abs (x secret - 200) + abs (y secret - 200) <= d)
  where
    limit = 50
    d = 100

{-# ANN module ("underapprox", "query", 1 :: Int) #-}

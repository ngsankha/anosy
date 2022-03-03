
{-@ LIQUID "--reflection" @-}

module SecretDefn where

import Ship

type Secret = Ship

{-@ reflect secretToLst @-}
secretToLst :: Secret -> [Int]
secretToLst l = [capacity l, x l, y l]

{-@ reflect first @-}
first :: (a, b) -> a
first (x, _) = x

{-@ reflect second @-}
second :: (a, b) -> b
second (_, x) = x

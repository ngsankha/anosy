
{-@ LIQUID "--reflection" @-}

module SecretDefn where

import Birthday

type Secret = DateOfBirth

{-@ reflect secretToLst @-}
secretToLst :: Secret -> [Int]
secretToLst l = [bday l, year l]

{-@ reflect first @-}
first :: (a, b) -> a
first (x, _) = x

{-@ reflect second @-}
second :: (a, b) -> b
second (_, x) = x

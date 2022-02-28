{-@ LIQUID "--reflection" @-}

module Photo where

{-@
data UserDetails = UserDetails {
  birthYear    :: Int,
  gender       :: Int,
  relationship :: Int
}
@-}
data UserDetails = UserDetails {
  birthYear    :: Int,
  gender       :: Int,
  relationship :: Int
}
{-# ANN UserDetails ([
  ("birthYear", (1900, 2010)),
  ("gender", (0, 1)),
  ("relationship", (0, 3))
  ] :: [(String, (Int, Int))]) #-}

{-@ reflect query @-}
query :: UserDetails -> Bool
query secret = let ageSat = (age >= 24) && (age <= 27) in
  ((gender secret) == 1) && ((relationship secret) == 3) && ageSat
  where
    age = 2010 - (birthYear secret)

{-# ANN module ("underapprox", "query") #-}
{-# ANN module ("overapprox", "query") #-}

{-@ LIQUID "--reflection" @-}

module Travel where

{-@
data UserDetails = UserDetails {
  country         :: Int,
  birthYear       :: Int,
  completedSchool :: Int,
  language        :: Int
}
@-}
data UserDetails = UserDetails {
  country         :: Int,
  birthYear       :: Int,
  completedSchool :: Int,
  language        :: Int
}
{-# ANN UserDetails ([
  ("country", (1, 200)),
  ("birthYear", (1900, 2011)),
  ("completedSchool", (0, 5)),
  ("language", (1, 50))
  ] :: [(String, (Int, Int))]) #-}

{-@ reflect query @-}
query :: UserDetails -> Bool
query secret = let mainCountry = (country secret == 1) || (country secret == 3) || (country secret == 8) || (country secret == 10) || (country secret == 18) in
  let island = (country secret == 169) || (country secret == 197) || (country secret == 194) || (country secret == 170) || (country secret == 206) || (country secret == 183) || (country secret == 188) in
    ((language secret) == 1) && (mainCountry || island) && (age >= 21) && ((completedSchool secret) >= 4)
  where
    age = 2010 - (birthYear secret)

{-# ANN module ("underapprox", "query") #-}
{-# ANN module ("overapprox", "query") #-}

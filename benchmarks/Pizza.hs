{-@ LIQUID "--reflection" @-}

module Pizza where

import Prelude

{-@
data UserDetails = UserDetails {
  schoolType :: Int,
  birthYear  :: Int,
  addressLat :: Int,
  addressLong:: Int
}
@-}
data UserDetails = UserDetails {
  schoolType :: Int,
  birthYear  :: Int,
  addressLat :: Int,
  addressLong:: Int
}
{-# ANN UserDetails ([
  ("schoolType", (0, 4)),
  ("birthYear", (1900, 2002)),
  ("addressLat", (38867884, 39103178)),
  ("addressLong", (76825926, 77058199))
  ] :: [(String, (Int, Int))]) #-}

{-@ reflect query @-}
query :: UserDetails -> Bool
query secret = let inSchool = ((schoolType secret) >= 4) in
  let ageCriteria = (age >= 18 && age <= 28) in
    let inBox = ((addressLat secret) <= ulLat) && ((addressLat secret) >= lrLat) && ((addressLong secret) <= ulLong) && ((addressLong secret) >= lrLong) in
      (inSchool || ageCriteria) && inBox
  where
    age = 2010 - (birthYear secret)
    lrLat = 38967884
    ulLat = 39003178
    lrLong = 76925926
    ulLong = 76958199

{-# ANN module ("underapprox", "query", 1 :: Int) #-}

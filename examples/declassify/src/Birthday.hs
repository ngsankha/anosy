{-@ LIQUID "--reflection" @-}

module Birthday where

-- The query and the secret
-- The ANN for DateOfBirth provides the bounds for synthesis
-- The ANN for module directs what kind of approximation to synthesize

{-@
data DateOfBirth = DateOfBirth {
  bday :: Int,
  year :: Int
}
@-}
data DateOfBirth = DateOfBirth {
  bday :: Int,
  year :: Int
} deriving (Eq, Show)
{-# ANN DateOfBirth ([
  ("bday", (0, 364)),
  ("year", (1956, 1992))
  ] :: [(String, (Int, Int))]) #-}

{-@ reflect query @-}
query :: DateOfBirth -> Bool
query secret = ((bday secret) >= cday) && ((cday + 7) > (bday secret))
  where
    cday = 260

{-# ANN module ("underapprox", "query", 1 :: Int) #-}
{-@ LIQUID "--reflection" @-}

module Birthday where

{-@
data DateOfBirth = DateOfBirth {
  bday :: Int,
  year :: Int
}
@-}
data DateOfBirth = DateOfBirth {
  bday :: Int,
  year :: Int
}
{-# ANN DateOfBirth ([
  ("bday", (0, 364)),
  ("year", (1956, 1992))
  ] :: [(String, (Int, Int))]) #-}

{-@ reflect query @-}
query :: DateOfBirth -> Bool
query secret = ((bday secret) >= cday) && ((cday + 7) > (bday secret))
  where
    cday = 260

{-# ANN module ("sound", "query") #-}
{-# ANN module ("complete", "query") #-}

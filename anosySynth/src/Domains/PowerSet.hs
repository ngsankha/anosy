module Domains.PowerSet where

data IntRange = IntRange {
  lower :: Int
, upper :: Int
}

data Range = Range {
  bounds :: [IntRange]
}

data PowerSet = PowerSet {
  pos :: [Range]
, neg :: [Range]
}

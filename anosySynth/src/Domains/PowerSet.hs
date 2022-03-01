{-# LANGUAGE QuasiQuotes #-}

module Domains.PowerSet where

import Data.String.Interpolate (i)
import Utils (first, findNum)
import Language.SMT.ToSMT (sepBy)

data IntRange = IntRange {
  lower :: Integer
, upper :: Integer
}

data Range = Range {
  bounds :: [IntRange]
}

data PowerSet = PowerSet {
  pos :: [Range]
, neg :: [Range]
}

mkEmptyPowerSet :: PowerSet
mkEmptyPowerSet = PowerSet [] []

mkPowerSet :: PowerSet -> [(String, (Int, Int))] -> [(String, Integer)] -> Bool -> PowerSet
mkPowerSet init dataFields model True  = PowerSet ((pos init) ++ [item]) (neg init)
  where item = Range (map (\x -> let label = (first x) in
              IntRange (findNum (label ++ "min") model) (findNum (label ++ "max") model)) dataFields)
mkPowerSet init dataFields model False = PowerSet (pos init) ((neg init) ++ [item])
  where item = Range (map (\x -> let label = (first x) in
              IntRange (findNum (label ++ "min") model) (findNum (label ++ "max") model)) dataFields)

class ToHs a where 
  toHs :: a -> String

instance ToHs IntRange where
  toHs (IntRange l u) = [i|(IntRange #{l} #{u})|]

instance ToHs Range where
  toHs (Range b) = sepBy ", " (map toHs b)

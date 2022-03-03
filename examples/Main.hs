module Main where

import ShipGen
import PowerSet
import Interval

main = do
  print (sizePowerset fst)
  print (sizePowerset snd)
  where
    (fst, snd) = underapproxInd

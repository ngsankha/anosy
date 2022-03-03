
{-# LANGUAGE RecordWildCards #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module ShipGen where

import Ship
import SecretDefn
import Interval (IntRange(..), Range(..), betweenSecret, betweenSecretRec, betweenInt)
import PowerSet


{-@ underapprox :: response: Bool
                -> prior: PowerSet
                -> {post:PowerSet<{l:Secret | response <=> query l}, {\_ -> True}> | subset post prior  }
@-}
underapprox :: Bool -> PowerSet -> PowerSet
underapprox response prior = case response of
  True  -> prior `intersectPowerSet` (first  underapproxInd)
  False -> prior `intersectPowerSet` (second underapproxInd)


{-@
underapproxInd :: (PowerSet<{l:Secret |      query l }, {\_ -> True}>,
                   PowerSet<{l:Secret | not (query l)}, {\_ -> True}>)
@-}
underapproxInd :: (PowerSet, PowerSet)
underapproxInd = ((PowerSet [(Range [(IntRange 51 100), (IntRange 167 233), (IntRange 133 267)] propEmpty propEmpty)] []
 propTruePos propEmpty),
                  (PowerSet [(Range [(IntRange 0 100), (IntRange 0 500), (IntRange 301 500)] propEmpty propEmpty)] []
 propFalsePos propEmpty))


{-@ propTruePos :: li:{Secret | 51 <= capacity li && capacity li <= 100 && 167 <= x li && x li <= 233 && 133 <= y li && y li <= 267}
               -> {l:Secret <{v:Secret | True <=> query v}> | l = li} @-}
propTruePos :: Secret -> Secret 
propTruePos li = li


{-@ propFalsePos :: li:{Secret | 0 <= capacity li && capacity li <= 100 && 0 <= x li && x li <= 500 && 301 <= y li && y li <= 500}
                  -> {l:Secret<{v:Secret | False <=> query v}> | l = li }  @-}
propFalsePos :: Secret -> Secret 
propFalsePos li = li


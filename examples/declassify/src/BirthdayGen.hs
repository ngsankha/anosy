
{-# LANGUAGE RecordWildCards #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module BirthdayGen where

import Birthday
import SecretDefn
import Interval (IntRange(..), Range(..), betweenSecret, betweenSecretRec, betweenInt)
import PowerSet


{-@ overapprox :: response: Bool
               -> prior: PowerSet
               -> {post:PowerSet<{\_ -> True}, {l:Secret | (not (response <=> query l)) || (not (secretInPowerset l prior)) }> | true }
@-}
overapprox :: Bool -> PowerSet -> PowerSet
overapprox response prior = case response of
  True  -> refine prior `intersectPowerSet` (first  overapproxInd)
  False -> refine prior `intersectPowerSet` (second overapproxInd)


{-@
overapproxInd :: (PowerSet<{\_ -> True}, {l:Secret | (not (query l)) }>,
                  PowerSet<{\_ -> True}, {l:Secret |       query l   }>)
@-}
overapproxInd :: (PowerSet, PowerSet)
overapproxInd = ((PowerSet [(Range [(IntRange 260 266), (IntRange 1956 1992)] propEmpty propEmpty)] []
 propEmpty propCompleteTruePos),
                 (PowerSetFull propEmpty))


{-@ assume propCompleteTruePos :: li:{Secret | (not (260 <= bday li && bday li <= 266 && 1956 <= year li && year li <= 1992))}
               -> {l:Secret <{v:Secret | False <=> query v}> | l = li} @-}
propCompleteTruePos :: Secret -> Secret 
propCompleteTruePos li = li




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
underapproxInd = ((PowerSet [(Range [(IntRange 260 266), (IntRange 1956 1992)] propEmpty propEmpty)] []
 propTruePos propEmpty),
                  (PowerSet [(Range [(IntRange 0 259), (IntRange 1956 1992)] propEmpty propEmpty)] []
 propFalsePos propEmpty))


{-@ propTruePos :: li:{Secret | 260 <= bday li && bday li <= 266 && 1956 <= year li && year li <= 1992}
               -> {l:Secret <{v:Secret | True <=> query v}> | l = li} @-}
propTruePos :: Secret -> Secret 
propTruePos li = li


{-@ propFalsePos :: li:{Secret | 0 <= bday li && bday li <= 259 && 1956 <= year li && year li <= 1992}
                  -> {l:Secret<{v:Secret | False <=> query v}> | l = li }  @-}
propFalsePos :: Secret -> Secret 
propFalsePos li = li


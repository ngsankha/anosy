{-# LANGUAGE QuasiQuotes #-}

module LiquidGenerator where

import Data.String.Interpolate (i)
import Language.SMT.ToSMT (toSMT, sepBy)
import Utils (first, findNum)
import Domains.PowerSet (PowerSet(..), Range(..), toHs, lower, upper)

secretDefn :: String -> String -> [(String, (Int, Int))] -> String
secretDefn mod secretType dataFields = [i|
{-@ LIQUID "--reflection" @-}

module SecretDefn where

import #{mod}

type Secret = #{secretType}

{-@ reflect secretToLst @-}
secretToLst :: Secret -> [Int]
secretToLst l = [#{sepBy ", " (map (\x -> (first x) ++ " l") dataFields)}]

{-@ reflect first @-}
first :: (a, b) -> a
first (x, _) = x

{-@ reflect second @-}
second :: (a, b) -> b
second (_, x) = x
|]

liquidHeader :: String -> String
liquidHeader mod = [i|
{-# LANGUAGE RecordWildCards #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module #{mod}Gen where

import #{mod}
import SecretDefn
import Interval (IntRange(..), Range(..), betweenSecret, betweenSecretRec, betweenInt)
import PowerSet
|]

underapprox :: String -> String
underapprox func = [i|
{-@ underapprox :: response: Bool
                -> prior: PowerSet
                -> {post:PowerSet<{l:Secret | response <=> #{func} l}, {\\_ -> True}> | subset post prior  }
@-}
underapprox :: Bool -> PowerSet -> PowerSet
underapprox response prior = case response of
  True  -> prior `intersectPowerSet` (first  underapproxInd)
  False -> prior `intersectPowerSet` (second underapproxInd)
|]

underapproxInd :: String -> PowerSet -> PowerSet -> String
underapproxInd func modelTrue modelFalse = [i|
{-@
underapproxInd :: (PowerSet<{l:Secret |      #{func} l }, {\\_ -> True}>,
                   PowerSet<{l:Secret | not (#{func} l)}, {\\_ -> True}>)
@-}
underapproxInd :: (PowerSet, PowerSet)
underapproxInd = ((PowerSet #{toHs modelTrue} propTruePos propEmpty),
                  (PowerSet #{toHs modelFalse} propFalsePos propEmpty))
|]

overapprox :: String -> String
overapprox func = [i|
{-@ overapprox :: response: Bool
               -> prior: PowerSet
               -> {post:PowerSet<{\\_ -> True}, {l:Secret | (not (response <=> #{func} l)) || (not (secretInPowerset l prior)) }> | true }
@-}
overapprox :: Bool -> PowerSet -> PowerSet
overapprox response prior = case response of
  True  -> refine prior `intersectPowerSet` (first  overapproxInd)
  False -> refine prior `intersectPowerSet` (second overapproxInd)
|]

overapproxInd :: String -> PowerSet -> PowerSet -> String
overapproxInd func modelTrue modelFalse = [i|
{-@
overapproxInd :: (PowerSet<{\\_ -> True}, {l:Secret | (not (#{func} l)) }>,
                  PowerSet<{\\_ -> True}, {l:Secret |       #{func} l   }>)
@-}
overapproxInd :: (PowerSet, PowerSet)
overapproxInd = ((PowerSet #{toHs modelTrue} propEmpty propCompleteTruePos),
                 (PowerSetFull propEmpty))
|]

-- rangeCon :: Range -> String
-- rangeCon dataFields model = sepBy ", " (map (\x -> let label = (first x) in
--   [i|(IntRange #{findNum (label ++ "min") model} #{findNum (label ++ "max") model})|]) dataFields)

propTruePos :: [(String, (Int, Int))] -> PowerSet -> String
propTruePos dataFields model = [i|
{-@ propTruePos :: li:{Secret | #{boundsExpr dataFields model}}
               -> {l:Secret <{v:Secret | True <=> query v}> | l = li} @-}
propTruePos :: Secret -> Secret 
propTruePos li = li
|]

propCompleteTruePos :: [(String, (Int, Int))] -> PowerSet -> String
propCompleteTruePos dataFields model = [i|
{-@ assume propCompleteTruePos :: li:{Secret | #{negBoundsExpr dataFields model}}
               -> {l:Secret <{v:Secret | False <=> query v}> | l = li} @-}
propCompleteTruePos :: Secret -> Secret 
propCompleteTruePos li = li
|]

propCompleteFalsePos :: [(String, (Int, Int))] -> PowerSet -> String
propCompleteFalsePos dataFields model = [i|
{-@ assume propCompleteFalsePos :: li:{Secret | #{negBoundsExpr dataFields model}}
               -> {l:Secret <{v:Secret | False <=> query v}> | l = li} @-}
propCompleteFalsePos :: Secret -> Secret 
propCompleteFalsePos li = li
|]

boundsExpr :: [(String, (Int, Int))] -> PowerSet -> String
boundsExpr dataFields (PowerSet pos neg) =
  (sepBy " || " (map (boundsExprRange dataFields) pos)) ++
  (negBoundsExprSub dataFields neg)

boundsExprRange :: [(String, (Int, Int))] -> Range -> String
boundsExprRange dataFields (Range b) = sepBy " && " (map (\(x, y) -> let label = (first x) in
  [i|#{lower y} <= #{label} li && #{label} li <= #{upper y}|]) (zip dataFields b))

negBoundsExprSub :: [(String, (Int, Int))] -> [Range] -> String
negBoundsExprSub dataFields [] = ""
negBoundsExprSub dataFields ranges = " && (not (" ++ (sepBy " || " (map (boundsExprRange dataFields) ranges)) ++ "))"

negBoundsExpr :: [(String, (Int, Int))] -> PowerSet -> String
negBoundsExpr dataFields pset = [i|(not (#{boundsExpr dataFields pset}))|]

-- negBoundsExprRange :: [(String, (Int, Int))] -> Range -> String
-- negBoundsExpr dataFields (Range b) = sepBy " || " (map (\(x, y) -> let label = (first x) in
--   [i|#{label} li < #{lower y} || #{upper y} < #{label} li|]) (zip dataFields b))

propEmpty :: String
propEmpty = [i|
{-@ propEmpty :: li:Secret -> {lr:Secret | li = lr } @-}
propEmpty :: Secret -> Secret 
propEmpty li = li
|]

propFalsePos :: [(String, (Int, Int))] -> PowerSet -> String
propFalsePos dataFields model = [i|
{-@ propFalsePos :: li:{Secret | #{boundsExpr dataFields model}}
                  -> {l:Secret<{v:Secret | False <=> query v}> | l = li }  @-}
propFalsePos :: Secret -> Secret 
propFalsePos li = li
|]

liquidTheorem :: [(String, (Int, Int))] -> ((String, String, Int), (PowerSet, PowerSet)) -> String
liquidTheorem dataFields (("underapprox", func, _), (trueModel, falseModel)) = [i|
#{underapprox func}
#{underapproxInd func trueModel falseModel}
#{propTruePos dataFields trueModel}
#{propFalsePos dataFields falseModel}
|]
liquidTheorem dataFields (("overapprox",  func, _), (trueModel, falseModel)) = [i|
#{overapprox func}
#{overapproxInd func trueModel falseModel}
#{propCompleteTruePos dataFields trueModel}
|]
liquidTheorem _ _ = error "unexpected input"

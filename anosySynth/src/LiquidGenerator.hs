{-# LANGUAGE QuasiQuotes #-}

module LiquidGenerator where

import Data.String.Interpolate (i)
import Language.SMT.ToSMT (toSMT, sepBy)
import Utils (first, findNum)
import Domains.PowerSet (Range(..), toHs, lower, upper)

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
import Interval
|]

underapprox :: String -> String
underapprox func = [i|
{-@ underapprox :: response: Bool
                -> prior: Range
                -> {post:Range<{l:Secret | response <=> #{func} l}, {\\_ -> True}> | subsetRange post prior  }
@-}
underapprox :: Bool -> Range -> Range
underapprox response prior = case response of
  True  -> prior `intersect` (first  underapproxInd)
  False -> prior `intersect` (second underapproxInd)
|]

underapproxInd :: String -> Range -> Range -> String
underapproxInd func modelTrue modelFalse = [i|
{-@
underapproxInd :: (Range<{l:Secret |      #{func} l }, {\\_ -> True}>,
                   Range<{l:Secret | not (#{func} l)}, {\\_ -> True}>)
@-}
underapproxInd :: (Range, Range)
underapproxInd = (Range [#{toHs modelTrue}] propTruePos propEmpty,
                  Range [#{toHs modelFalse}] propFalsePos propEmpty)
|]

overapprox :: String -> String
overapprox func = [i|
{-@ overapprox :: response: Bool
               -> prior: Range
               -> {post:Range<{\\_ -> True}, {l:Secret | (not (response <=> #{func} l)) || (not (betweenSecret l prior)) }> | true }
@-}
overapprox :: Bool -> Range -> Range
overapprox response prior = case response of
  True  -> refine prior `intersect` (first  overapproxInd)
  False -> refine prior `intersect` (second overapproxInd)
|]

overapproxInd :: String -> Range -> Range -> String
overapproxInd func modelTrue modelFalse = [i|
{-@
overapproxInd :: (Range<{\\_ -> True}, {l:Secret | (not (#{func} l)) }>,
                  Range<{\\_ -> True}, {l:Secret |       #{func} l   }>)
@-}
overapproxInd :: (Range, Range)
overapproxInd = (Range [#{toHs modelTrue}] propEmpty propCompleteTruePos,
                 RangeFull propEmpty)
|]

-- rangeCon :: Range -> String
-- rangeCon dataFields model = sepBy ", " (map (\x -> let label = (first x) in
--   [i|(IntRange #{findNum (label ++ "min") model} #{findNum (label ++ "max") model})|]) dataFields)

propTruePos :: [(String, (Int, Int))] -> Range -> String
propTruePos dataFields model = [i|
{-@ propTruePos :: li:{Secret | #{boundsExpr dataFields model}}
               -> {l:Secret <{v:Secret | True <=> query v}> | l = li} @-}
propTruePos :: Secret -> Secret 
propTruePos li = li
|]

propCompleteTruePos :: [(String, (Int, Int))] -> Range -> String
propCompleteTruePos dataFields model = [i|
{-@ assume propCompleteTruePos :: li:{Secret | #{negBoundsExpr dataFields model}}
               -> {l:Secret <{v:Secret | False <=> query v}> | l = li} @-}
propCompleteTruePos :: Secret -> Secret 
propCompleteTruePos li = li
|]

boundsExpr :: [(String, (Int, Int))] -> Range -> String
boundsExpr dataFields (Range b) = sepBy " && " (map (\(x, y) -> let label = (first x) in
  [i|#{lower y} <= #{label} li && #{label} li <= #{upper y}|]) (zip dataFields b))

negBoundsExpr :: [(String, (Int, Int))] -> Range -> String
negBoundsExpr dataFields (Range b) = sepBy " || " (map (\(x, y) -> let label = (first x) in
  [i|#{label} li < #{lower y} || #{upper y} < #{label} li|]) (zip dataFields b))

propEmpty :: String
propEmpty = [i|
{-@ propEmpty :: li:Secret -> {lr:Secret | li = lr } @-}
propEmpty :: Secret -> Secret 
propEmpty li = li
|]

propFalsePos :: [(String, (Int, Int))] -> Range -> String
propFalsePos dataFields model = [i|
{-@ propFalsePos :: li:{Secret | #{boundsExpr dataFields model}}
                  -> {l:Secret<{v:Secret | False <=> query v}> | l = li }  @-}
propFalsePos :: Secret -> Secret 
propFalsePos li = li
|]

liquidTheorem :: [(String, (Int, Int))] -> ((String, String, Int), (Range, Range)) -> String
liquidTheorem dataFields (("underapprox", func, 1), (trueModel, falseModel)) = [i|
#{underapprox func}
#{underapproxInd func trueModel falseModel}
#{propTruePos dataFields trueModel}
#{propFalsePos dataFields falseModel}
|]
liquidTheorem dataFields (("overapprox",  func, 1), (trueModel, falseModel)) = [i|
#{overapprox func}
#{overapproxInd func trueModel falseModel}
#{propCompleteTruePos dataFields trueModel}
|]
liquidTheorem _ _ = error "unexpected input"

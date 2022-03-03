{-# LANGUAGE QuasiQuotes #-}

module Solver where

import Data.String.Interpolate (i)
import GhcPlugins (TyCon, CoreProgram)
import Annotations (Annotation)
import Unique (Unique)
import qualified Language.SMT.Constraints as Constraints
import Text.Megaparsec (errorBundlePretty, ParseErrorBundle)
import Data.Void (Void)
import Z3Interface (Z3SATResult, checkSATWithZ3)
import Language.SMT.ToSMT (toSMT, sepBy)
import Control.Monad.IO.Class (liftIO)
import Data.List (find)
import Data.Foldable (for_)
import Text.Printf (printf)
import Data.Char (toLower)
import Utils (first, findNum)
import Domains.PowerSet (PowerSet(..), Range(..), IntRange(..))

querySMTEncode :: [TyCon] -> CoreProgram -> String
querySMTEncode tycons hsBinds = secretType ++ querySMT
  where
    secretType = toSMT tycons
    querySMT = toSMT hsBinds

smtModels :: [TyCon]
          -> CoreProgram
          -> Annotation
          -> [(Unique, [[(String, (Int, Int))]])]
          -> [(String, (Int, Int))]
          -> (String, String, Int)
          -> PowerSet
          -> Bool
          -> IO (Either String Range)
smtModels tycons hsBinds ann bounds dataFields modann pset response = do
  let secretType = toSMT tycons
  let querySMT = toSMT hsBinds
  let absSecretType = Constraints.absSMT ann (head bounds)
  let betweeenQuery = Constraints.betweeenSMT ann (head bounds) pset
  let boundsAssert = Constraints.searchBounds dataFields
  let solverAssert = Constraints.solverQuery ann modann dataFields (head bounds) pset response
  let optAssert = Constraints.optQuery modann dataFields

  let query = smtHeader ++
                  Constraints.intRangeSMT ++
                  secretType ++
                  querySMT ++
                  absSecretType ++
                  betweeenQuery ++
                  boundsAssert ++
                  solverAssert ++
                  optAssert ++
                  smtFooter

  -- liftIO $ putStrLn $ query

  model <- liftIO $ checkSATWithZ3 (smtFileName "foo") $ query
  -- falseModel <- liftIO $ checkSATWithZ3 (smtFileName "foo") $ falseQuery
  return (modelToList dataFields model)

modelToList :: [(String, (Int, Int))] -> Either (ParseErrorBundle String Void) (Z3SATResult, [(String, Integer)]) -> Either String Range
modelToList dataFields model = case model of
    Left e -> Left (errorBundlePretty e)
    Right (_trueSat, funs) -> case (modelToRange dataFields funs) of
      Left e -> Left e
      Right r -> Right r


-- findNum :: (Foldable t, Eq a) => a -> t (a, c) -> c
-- findNum label = (\(Just t)->snd t) . find (\x -> (fst x == label))

printSmtModel :: IO (Either String (Z3SATResult, [(String, Integer)])) -> IO ()
printSmtModel result = do
  inner <- result
  case inner of
    Left e -> liftIO $ putStrLn $ "Error: " ++ e
    Right (satResult, funs) -> do
      for_ funs $ \(name, value) ->
        liftIO $ putStrLn $ printf "%s = %d" name value
      liftIO $ putStrLn $ printf "result=%s" (show satResult)

smtFileName :: String -> String 
smtFileName name = "./out/" ++ map toLower name ++ ".smt2"

smtHeader :: String
smtHeader = [i|
(set-option :opt.priority pareto)
(set-option :produce-models true)
(set-option :timeout 10000)
|]

smtFooter :: String
smtFooter = [i|
(check-sat)
(get-model)
(exit)
|]

modelToIntRange :: [(String, (Int, Int))] -> [(String, Integer)] -> Either String [IntRange]
modelToIntRange [] model = Right []
modelToIntRange (hd:tl) model =
  let lower = (findNum (label ++ "min") model) in
  let upper = (findNum (label ++ "max") model) in
  case (lower, upper) of
    (Right l, Right u) -> case (modelToIntRange tl model) of
      Left e -> Left e
      Right rs -> Right ([(IntRange l u)] ++ rs)
    (_, _ ) -> Left "model not found"
  where
    label = first hd

modelToRange :: [(String, (Int, Int))] -> [(String, Integer)] -> Either String Range
modelToRange dataFields model = case (modelToIntRange dataFields model) of
  Left e -> Left e
  Right rs -> Right (Range rs)
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

smtModels :: [TyCon] -> CoreProgram -> Annotation -> [(Unique, [[(String, (Int, Int))]])] -> [(String, (Int, Int))] -> (String, String, Int) -> IO ([(String, Integer)], [(String, Integer)])
smtModels tycons hsBinds ann bounds dataFields modann = do
  let secretType = toSMT tycons
  let querySMT = toSMT hsBinds
  let absSecretType = Constraints.absSMT ann (head bounds)
  let betweeenQuery = Constraints.betweeenSMT ann (head bounds)
  let boundsAssert = Constraints.searchBounds dataFields
  let solverAssertTrue = Constraints.solverQuery ann modann dataFields True
  let solverAssertFalse = Constraints.solverQuery ann modann dataFields False
  let optAssert = Constraints.optQuery modann dataFields

  let trueQuery = smtHeader ++
                  Constraints.intRangeSMT ++
                  secretType ++
                  querySMT ++
                  absSecretType ++
                  betweeenQuery ++
                  boundsAssert ++
                  solverAssertTrue ++
                  optAssert ++
                  smtFooter
  let falseQuery = smtHeader ++
                   Constraints.intRangeSMT ++
                   secretType ++
                   querySMT ++
                   absSecretType ++
                   betweeenQuery ++
                   boundsAssert ++
                   solverAssertFalse ++
                   optAssert ++
                   smtFooter

  -- liftIO $ putStrLn $ trueQuery
  -- liftIO $ putStrLn $ falseQuery

  trueModel <- liftIO $ checkSATWithZ3 (smtFileName "foo") $ trueQuery
  falseModel <- liftIO $ checkSATWithZ3 (smtFileName "foo") $ falseQuery
  return (modelToList trueModel, modelToList falseModel)

modelToList :: Either (ParseErrorBundle String Void) (Z3SATResult, [(String, Integer)]) -> [(String, Integer)]
modelToList model = case model of
    Left e -> error (errorBundlePretty e)
    Right (_trueSat, funs) -> funs


findNum :: (Foldable t, Eq a) => a -> t (a, c) -> c
findNum label = (\(Just t)->snd t) . find (\x -> (fst x == label))

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

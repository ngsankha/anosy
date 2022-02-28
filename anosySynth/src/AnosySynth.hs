{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}

module AnosySynth (plugin) where

import Data.String.Interpolate ( i )
import GhcPlugins
import Language.Ghc.Misc ()
import Language.SMT.ToSMT (toSMT, sepBy)
import Data.Char (toLower)
import Data.List (find)
import Data.Word (Word8)
import Text.Printf
import Data.Foldable (for_)
import Z3Interface
import qualified Domains.Range as Range
import LiquidGenerator (liquidTheorem, liquidHeader, secretDefn)
import Text.Megaparsec (errorBundlePretty, ParseErrorBundle)
import Data.Void (Void)
import Utils (first, second, annName, dataAnnot, modAnnot)

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo =
  return (CoreDoPluginPass "anosySynth" pass : todo)

smtModels :: [TyCon] -> CoreProgram -> Annotation -> [(Unique, [[(String, (Int, Int))]])] -> [(String, (Int, Int))] -> (String, String) -> IO ([(String, Integer)], [(String, Integer)])
smtModels tycons hsBinds ann bounds dataFields modann = do
  let secretType = toSMT tycons
  let querySMT = toSMT hsBinds
  let absSecretType = Range.absSMT ann (head bounds)
  let betweeenQuery = Range.betweeenSMT ann (head bounds)
  let boundsAssert = Range.searchBounds dataFields
  let solverAssertTrue = Range.solverQuery ann modann dataFields True
  let solverAssertFalse = Range.solverQuery ann modann dataFields False
  let optAssert = Range.optQuery modann dataFields

  let trueQuery = smtHeader ++
                  Range.intRangeSMT ++
                  secretType ++
                  querySMT ++
                  absSecretType ++
                  betweeenQuery ++
                  boundsAssert ++
                  solverAssertTrue ++
                  optAssert ++
                  smtFooter
  let falseQuery = smtHeader ++
                   Range.intRangeSMT ++
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

pass :: ModGuts -> CoreM ModGuts
pass modguts  = do 
    let name     = showSDocUnsafe $ pprModule $ mg_module modguts
    let hsBinds  = mg_binds modguts
    let tycons   = mg_tcs modguts
    let annots   = mg_anns modguts

    -- -- Print initial Haskell Binds 
    -- liftIO $ putStrLn $ "\n--- Haskell Binds: ---\n" 
    -- liftIO $ putStrLn $ show hsBinds 
    -- -- Print Tycons translation
    -- liftIO $ putStrLn $ "\n--- Haskell TyCons: ---\n"
    -- liftIO $ putStrLn $ show tycons  
    -- -- Write translation into the .smt file 
    -- liftIO $ putStrLn $ toSMT tycons
    -- liftIO $ putStrLn $ toSMT hsBinds 
    -- -- Write translation query
    -- liftIO $ putStrLn $ show annots
    let bounds = nonDetUFMToList $ deserializeAnns (deserializeWithData :: [Word8] -> [(String, (Int, Int))]) $ mkAnnEnv (filter dataAnnot annots)
    let approxes = nonDetUFMToList $ deserializeAnns (deserializeWithData :: [Word8] -> (String, String)) $ mkAnnEnv (filter modAnnot annots)
    let ann = head (filter dataAnnot annots)
    let dataFields = head (second (head bounds))
    let modanns = second (head approxes)
    z3solns <- liftIO $ sequence (map (smtModels tycons hsBinds ann bounds dataFields) modanns)
    let liquidThms = sepBy "\n" (map (liquidTheorem dataFields) (zip modanns z3solns))
    let liquidHead = liquidHeader name
    
    -- liftIO $ putStrLn $ liquidThms
    
    -- trueModel <- liftIO $ checkSATWithZ3 (smtFileName name) $ trueQuery
    -- falseModel <- liftIO $ checkSATWithZ3 (smtFileName name) $ falseQuery

    -- liftIO $ writeFile (smtFileName name) trueQuery
    -- liftIO $ printSmtModel (checkSATWithZ3 (smtFileName name) $ falseQuery)
    -- liftIO $ writeFile (liquidFileName name) (liquidText name trueModel falseModel)

    -- liftIO $ putStrLn $ (liquidHeader name (annName ann) dataFields)
    liftIO $ writeFile (liquidFileName name) (liquidHead ++ liquidThms)
    liftIO $ writeFile ("./SecretDefn.hs") (secretDefn name (annName ann) dataFields)
    
    bindsOnlyPass (mapM return) modguts

modelToList :: Either (ParseErrorBundle String Void) (Z3SATResult, [(String, Integer)]) -> [(String, Integer)]
modelToList model = case model of
    Left e -> error (errorBundlePretty e)
    Right (_trueSat, funs) -> funs


-- genLiquid :: String -> [(String, Integer)] -> [(String, Integer)] -> String
-- genLiquid name trueFuns falseFuns = hsGenSrc name
--                                         (findNum "xmin" trueFuns)
--                                         (findNum "xmax" trueFuns)
--                                         (findNum "ymin" trueFuns)
--                                         (findNum "ymax" trueFuns)
--                                         (findNum "xmin" falseFuns)
--                                         (findNum "xmax" falseFuns)
--                                         (findNum "ymin" falseFuns)
--                                         (findNum "ymax" falseFuns)

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

liquidFileName :: String -> String 
liquidFileName name = "./" ++ name ++ "Gen.hs"

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

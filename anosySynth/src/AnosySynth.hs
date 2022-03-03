{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}

module AnosySynth (plugin) where

import Data.String.Interpolate (i)
import GhcPlugins
import Language.Ghc.Misc ()
import Language.SMT.ToSMT (toSMT, sepBy)
import Data.List (find)
import Data.Word (Word8)
import qualified Language.SMT.Constraints as Constraints
import LiquidGenerator (liquidTheorem, liquidHeader, secretDefn)
import Utils (first, second, annName, dataAnnot, modAnnot, findNum)
import Solver (smtModels, querySMTEncode)
import Domains.PowerSet (IntRange(..), Range(..))
import Z3Interface (runPyMod)
import Domains.PowerSet (PowerSet(..), mkEmptyPowerSet)
import Text.Megaparsec (errorBundlePretty, ParseErrorBundle)
import Data.Void (Void)

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo =
  return (CoreDoPluginPass "anosySynth" pass : todo)

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
    let approxes = nonDetUFMToList $ deserializeAnns (deserializeWithData :: [Word8] -> (String, String, Int)) $ mkAnnEnv (filter modAnnot annots)
    let ann = head (filter dataAnnot annots)
    let dataFields = head (second (head bounds))
    let modanns = second (head approxes)
    let parAppSMTModels = smtModels tycons hsBinds ann bounds dataFields
    -- z3solns <- liftIO $ sequence (map parAppSMTModels modanns)

    psets <- liftIO $ sequence (map (tmpFn parAppSMTModels dataFields) modanns)
    -- psetTrue <- liftIO $ buildPSet mkEmptyPowerSet (head modanns) parAppSMTModels dataFields True
    -- psetFalse <- liftIO $ buildPSet mkEmptyPowerSet (head modanns) parAppSMTModels dataFields False

    -- liftIO $ putStrLn $ show $ psetFalse
    -- let ranges = map (\x -> (transformDataF (first x), transformDataF (second x))) z3solns
    -- let psets = [(psetTrue, psetFalse)]
    let liquidThms = sepBy "\n" (map (liquidTheorem dataFields) (zip modanns psets))
    let liquidHead = liquidHeader name

    -- liftIO $ putStrLn $ liquidThms
    -- liftIO $ writeFile "input.json" $ unpack $ encode $ (PyInput (querySMTEncode tycons hsBinds) dataFields modanns)
    -- liftIO $ runPyMod >>= putStrLn
    
    -- trueModel <- liftIO $ checkSATWithZ3 (smtFileName name) $ trueQuery
    -- falseModel <- liftIO $ checkSATWithZ3 (smtFileName name) $ falseQuery

    -- liftIO $ writeFile (smtFileName name) trueQuery
    -- liftIO $ printSmtModel (checkSATWithZ3 (smtFileName name) $ falseQuery)
    -- liftIO $ writeFile (liquidFileName name) (liquidText name trueModel falseModel)
    -- liftIO $ putStrLn $ (liquidHeader name (annName ann) dataFields)

    liftIO $ writeFile (liquidFileName name) (liquidHead ++ liquidThms)
    liftIO $ writeFile ("./SecretDefn.hs") (secretDefn name (annName ann) dataFields)
    
    bindsOnlyPass (mapM return) modguts

tmpFn :: ((String, String, Int) -> PowerSet -> Bool -> IO (Either String Range))
      -> [(String, (Int, Int))]
      -> (String, String, Int) -> IO (PowerSet, PowerSet)
tmpFn parAppSMTModels dataFields someAnn = do
      t1 <- buildPSet mkEmptyPowerSet someAnn parAppSMTModels dataFields True
      t2 <- buildPSet mkEmptyPowerSet someAnn parAppSMTModels dataFields False
      return (t1, t2)

buildPSet :: PowerSet
          -> (String, String, Int)
          -> ((String, String, Int) -> PowerSet -> Bool -> IO (Either String Range))
          -> [(String, (Int, Int))]
          -> Bool
          -> IO PowerSet
buildPSet pset@(PowerSet pos neg) action@("underapprox", func, 1) parApp dataFields response = do
  z3soln <- parApp action pset response
  case z3soln of
    Left e -> error e
    Right range -> return (PowerSet (pos ++ [range]) neg)
buildPSet pset action@(approx@"underapprox", func, k) parApp dataFields response = do
  psetSub <- buildPSet pset (approx, func, k - 1) parApp dataFields response
  -- liftIO $ putStrLn $ show $ psetSub
  z3soln <- parApp action psetSub response
  case z3soln of
    Left e -> return psetSub
    Right range -> return (PowerSet ((pos psetSub) ++ [range]) (neg psetSub))

buildPSet pset@(PowerSet pos neg) action@("overapprox", func, 1) parApp dataFields response = do
  z3soln <- parApp action pset response
  case z3soln of
    Left e -> error e
    Right range -> return (PowerSet (pos ++ [range]) neg)
buildPSet pset action@(approx@"overapprox", func, k) parApp dataFields response = do
  psetSub <- buildPSet pset (approx, func, k - 1) parApp dataFields response
  -- liftIO $ putStrLn $ show $ psetSub
  z3soln <- parApp action psetSub response
  case z3soln of
    Left e -> return psetSub
    Right range -> return (PowerSet (pos psetSub) ((neg psetSub) ++ [range]))


liquidFileName :: String -> String 
liquidFileName name = "./" ++ name ++ "Gen.hs"

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
import Domains.PowerSet (PowerSet(..), mkEmptyPowerSet)
import Text.Megaparsec (errorBundlePretty, ParseErrorBundle)
import Data.Void (Void)
import System.Exit (die)

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

    let bounds = nonDetUFMToList $ deserializeAnns (deserializeWithData :: [Word8] -> [(String, (Int, Int))]) $ mkAnnEnv (filter dataAnnot annots)
    let approxes = nonDetUFMToList $ deserializeAnns (deserializeWithData :: [Word8] -> (String, String, Int)) $ mkAnnEnv (filter modAnnot annots)
    let ann = head (filter dataAnnot annots)
    let dataFields = head (second (head bounds))
    let modanns = second (head approxes)
    let parAppSMTModels = smtModels tycons hsBinds ann bounds dataFields

    psets <- liftIO $ sequence (map (tmpFn parAppSMTModels dataFields) modanns)

    -- The following commented lines help with debugging. Uncomment them to log the intermediate values.
    -- psetTrue <- liftIO $ buildPSet mkEmptyPowerSet (head modanns) parAppSMTModels dataFields True
    -- psetFalse <- liftIO $ buildPSet mkEmptyPowerSet (head modanns) parAppSMTModels dataFields False
    -- liftIO $ putStrLn $ show $ psetFalse
    -- let ranges = map (\x -> (transformDataF (first x), transformDataF (second x))) z3solns
    -- let psets = [(psetTrue, psetFalse)]

    let liquidThms = sepBy "\n" (map (liquidTheorem dataFields) (zip modanns psets))
    let liquidHead = liquidHeader name

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
    Left e -> die e
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
    Left e -> die e
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

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
import Solver (smtModels)
import Domains.PowerSet (IntRange(..), Range(..))

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
    z3solns <- liftIO $ sequence (map (smtModels tycons hsBinds ann bounds dataFields) modanns)
    let transformDataF = modelToRange dataFields
    let ranges = map (\x -> (transformDataF (first x), transformDataF (second x))) z3solns
    let liquidThms = sepBy "\n" (map (liquidTheorem dataFields) (zip modanns ranges))
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

modelToRange :: [(String, (Int, Int))] -> [(String, Integer)] -> Range
modelToRange dataFields model = Range (map (\x -> let label = (first x) in
  IntRange (findNum (label ++ "min") model) (findNum (label ++ "max") model)) dataFields)


liquidFileName :: String -> String 
liquidFileName name = "./" ++ name ++ "Gen.hs"

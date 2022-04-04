module Z3Interface where

import Data.Maybe (mapMaybe)
import System.IO (BufferMode (..), hGetContents, hPutStrLn, hSetBuffering)
import System.Process
import Text.Megaparsec (parse)
import Text.Megaparsec.Char (char, string)
-- import Text.Printf (printf)
import Text.SExpression (Parser, SExpr (..), def, parseSExpr)
import Control.Applicative ((<|>))
import Control.Exception (evaluate)
import Control.Monad (void)
-- import Data.Foldable (for_)
import Data.Maybe (catMaybes)
import Text.Megaparsec.Error (ParseErrorBundle)
import Data.Void (Void)

-- The following code and dependencies are taken from
-- https://github.com/rcook/sexpr-parser

data Z3SATResult = Satisfied | Unsatisfied | Unknown deriving (Show)

data Z3Output = Z3Output Z3SATResult SExpr deriving (Show)

parseZ3SATResult :: Parser Z3SATResult
parseZ3SATResult = do
  s <- string "sat" <|> string "unsat" <|> string "unknown"
  void $ char '\n'
  case s of
    "sat" -> pure Satisfied
    "unknown" -> pure Unknown
    "unsat" -> pure Unsatisfied
    _ -> error "Unreachable"

parseZ3Output :: Parser Z3Output
parseZ3Output = Z3Output <$> parseZ3SATResult <*> parseSExpr def

checkSATWithZ3 :: String -> String -> IO (Either (ParseErrorBundle String Void) (Z3SATResult, [(String, Integer)]))
checkSATWithZ3 ctx input = do
  output <- withCreateProcess (proc "z3" ["-in"])
            { std_in = CreatePipe
            , std_out = CreatePipe
            , std_err = CreatePipe
            } $ \(Just hIn) (Just hOut) _ _ -> do
    hSetBuffering hIn NoBuffering
    hPutStrLn hIn input
    s <- hGetContents hOut
    void $ evaluate (length s)
    pure s
  case parse parseZ3Output ctx output of
    Left e -> pure $ Left e
    Right (Z3Output satResult f) -> pure $ Right (satResult, intFuns f)

intFuns :: SExpr -> [(String, Integer)]
-- intFuns (List (Atom "model" : fs) = mapMaybe p fs
intFuns (List fs) = catMaybes $ map p fs
  where
    p :: SExpr -> Maybe (String, Integer)
    p (List [Atom "define-fun", Atom name, List [], Atom "Int", Number num]) = Just (name, num)
    p _ = Nothing
intFuns _ = []


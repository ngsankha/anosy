{-|
Module      : Text.SExpression
Description : S-expression parser
Copyright   : (C) Richard Cook, 2019
Licence     : MIT
Maintainer  : rcook@rcook.org
Stability   : stable
Portability : portable

This module provides a 'parseSExpr' function which parses simple
s-expressions represented using the 'SExpr' type from 'String' input.

Here's a full example which uses <https://github.com/Z3Prover/z3 Z3> to
determine the satisfiability of a simple Boolean expression. It feeds
<http://smtlib.cs.uiowa.edu/language.shtml SMT-LIB v2>-format input to
Z3 and then parses the output (which uses a subset of Lisp-style
s-expressions) to display the satisfying assignment for the expression.

> module Main (main) where
>
> import Control.Applicative ((<|>))
> import Control.Exception (evaluate)
> import Control.Monad (void)
> import Data.Foldable (for_)
> import Data.List (sort)
> import Data.Maybe (catMaybes)
> import System.IO (BufferMode(..), hGetContents, hPutStrLn, hSetBuffering)
> import System.Process
> import Text.Megaparsec (parse)
> import Text.Megaparsec.Char (char, string)
> import Text.Printf (printf)
> import Text.SExpression (Parser, SExpr(..), parseSExpr, def)
> data Z3SATResult = Satisfied | Unsatisfied deriving Show
>
> data Z3Output = Z3Output Z3SATResult SExpr deriving Show
>
> main :: IO ()
> main = do
>     result <- checkSATWithZ3 "input.smt2" $
>         "(push)\n\
>         \(declare-const x bool)\n\
>         \(declare-const y bool)\n\
>         \(assert (and (not x) y))\n\
>         \(check-sat)\n\
>         \(get-model)\n\
>         \(pop)\n\
>         \(exit)\n"
>     case result of
>         Left e -> putStrLn $ "Error: " ++ e
>         Right (satResult, funs) -> do
>             for_ funs $ \(name, value) ->
>                 putStrLn $ printf "%s = %s" name (if value then "1" else "0")
>             putStrLn $ printf "result=%s" (show satResult)
>
> parseZ3SATResult :: Parser Z3SATResult
> parseZ3SATResult = do
>     s <- string "sat" <|> string "unsat"
>     void $ char '\n'
>     case s of
>         "sat" -> pure Satisfied
>         "unsat" -> pure Unsatisfied
>         _ -> error "Unreachable"
>
> parseZ3Output :: Parser Z3Output
> parseZ3Output = Z3Output <$> parseZ3SATResult <*> parseSExpr def
>
> checkSATWithZ3 :: String -> String -> IO (Either String (Z3SATResult, [(String, Bool)]))
> checkSATWithZ3 ctx input = do
>     output <- withCreateProcess (proc "z3" ["-in"])
>                         { std_in = CreatePipe
>                         , std_out = CreatePipe
>                         , std_err = Inherit
>                         } $ \(Just hIn) (Just hOut) _ _ -> do
>         hSetBuffering hIn NoBuffering
>         hPutStrLn hIn input
>         s <- hGetContents hOut
>         void $ evaluate (length s)
>         pure s
>     case parse parseZ3Output ctx output of
>         Left e -> pure $ Left (show e)
>         Right (Z3Output satResult f) -> pure $ Right (satResult, sort (boolFuns f))
>
> boolFuns :: SExpr -> [(String, Bool)]
> boolFuns (List (Atom "model" : fs)) = catMaybes $ map p fs
>     where
>         p :: SExpr -> Maybe (String, Bool)
>         p (List [Atom "define-fun", Atom name, List [], Atom "bool", Atom "false"]) = Just (name, False)
>         p (List [Atom "define-fun", Atom name, List [], Atom "bool", Atom "true"]) = Just (name, True)
>         p _ = Nothing
> boolFuns _ = []

This demonstrates how to run the parser with 'Text.Megaparsec.parse' and
'parseSExpr' as well as how to compose the s-expression parser with
other parsers to handle a composite format. It also shows how to
pattern-match on 'SExpr' to extract data from s-expressions.

-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Text.SExpression
    ( -- * Parser context
      Parser
    , -- * S-expression values
      SExpr(..)
    , -- * S-expression parser
      parseSExpr
    , -- * Polymorphic default value
      def
    ) where

import Data.Default (def)
import Text.SExpression.Internal (parseSExpr)
import Text.SExpression.Types (Parser, SExpr(..))

{-# LANGUAGE DeriveDataTypeable #-}

module PluginAnnotations where

import Data.Typeable
import Data.Data

data Domains = Rectangle deriving (Data, Typeable)

data Sound = Sound {
    query:: String,
    domain:: Domains
} deriving (Data, Typeable)

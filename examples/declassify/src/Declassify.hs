{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where 

import Prelude hiding (max, min)
import Anosy 
import LIO 
import LIO.DCLabel
import LIO.TCB (ioTCB, Labeled(..))
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Lazy
import Control.Monad.IO.Class
import Data.Hashable 
import Data.HashMap.Strict (fromList)
import SecretDefn
import Birthday
import BirthdayGen (underapprox, overapprox)
import PowerSet
import Interval (Range(..), IntRange(..))

-- The quantitative policy used to secure the data
-- Here we check that an adversary can not guess the possible user's birthday
-- below 100 choices
mypolicy :: (PowerSet, PowerSet) -> (Bool, Bool)
mypolicy (trueDom, falseDom) = (sizePowerset trueDom  > 100,
                                sizePowerset falseDom > 100)

instance AbsDom PowerSet where 
  contains elem dom = secretInPowerset elem dom
  subset dom1 dom2 = subsetPowerSet dom1 dom2
  intersect dom1 dom2 = intersectPowerSet dom1 dom2

-- The initial prior knowledge
initPrior :: PowerSet
initPrior = PowerSet [Range [(IntRange 0 364), (IntRange 1956 1992)] prop prop] [] prop prop

prop :: Secret -> Secret 
prop li = li

-- An LIO computation, to lookup birthday of an user
lookupUserBirthday :: String -> LIO DCLabel (Labeled DCLabel Secret)
lookupUserBirthday user = return $ LabeledTCB (user %% user) dob
  where
    dob = DateOfBirth 260 1980

instance Hashable Secret where 
   hashWithSalt x _ = x 

initState :: String -> LIO DCLabel (AnosyST PowerSet Secret)
initState name = do
  secret <- lookupUserBirthday name
  return AnosyST {initKnow = initPrior, policy = mypolicy, secrets = mempty}

-- This is the monad 
type MySecret = Secret
type ALIO = AnosyT PowerSet MySecret (LIO DCLabel) 
instance Unprotectable (Labeled DCLabel) where
  unprotect (LabeledTCB _l secret) = secret 


-- The initial state of the Anosy monad
initAnosy :: AnosyST PowerSet MySecret
initAnosy = AnosyST {initKnow = initPrior, policy = mypolicy, secrets = mempty, queries = qinfos}
  where qinfos = fromList [("query", QInfo query sound complete)]

-- Calling the synthesized underapprox and overapprox functions from the
-- synthesized `BirthdayGen.hs` file
sound :: PowerSet -> (PowerSet, PowerSet)
sound prior = (underapprox True prior, underapprox False prior)

complete :: PowerSet -> (PowerSet, PowerSet)
complete prior = (overapprox True prior, overapprox False prior)

-- Runs the LIO computation then does the bounded downgrade using the policy via Anosy
act :: String -> ALIO Bool  
act name = do 
  secret <- lift (lookupUserBirthday name)
  downgrade UnderApprox secret "query"

-- main function serves as an entrypoint
main :: IO ()
main = do
  response <- evalDC (evalStateT (act "Alice") initAnosy)
  putStrLn $ "Query response is: " <> show response

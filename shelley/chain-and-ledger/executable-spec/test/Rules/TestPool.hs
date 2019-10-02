{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Rules.TestPool where

import           Data.Map (Map, (!?))
import qualified Data.Maybe as Maybe (maybe)
import           Data.Word (Word64)

import           Hedgehog (Property, forAll, property, withTests)

import           Control.State.Transition.Generator (ofLengthAtLeast, trace)
import           Control.State.Transition.Trace (pattern SourceSignalTarget, signal, source,
                     sourceSignalTargets, target, _traceEnv)

import           BaseTypes ((==>))
import           Delegation.Certificates (cwitness)
import           LedgerState (_retiring, _stPools)
import           MockTypes (KeyHash, POOL, PState, StakePools)
import           PParams (_eMax)
import           Slot (Epoch (..), epochFromSlot)
import           STS.Pool (PoolEnv (..))
import           TxData (pattern KeyHashObj, pattern RegPool, pattern RetirePool,
                     pattern StakePools)


import           Ledger.Core (dom, (∈), (∉))
import           Test.Utils (assertAll)

-------------------------------
-- helper accessor functions --
-------------------------------

getRetiring :: PState -> Map KeyHash Epoch
getRetiring = _retiring

getStPools :: PState -> StakePools
getStPools = _stPools

------------------------------
-- Constants for Properties --
------------------------------

numberOfTests :: Word64
numberOfTests = 300

traceLen :: Word64
traceLen = 100

-------------------------
-- Properties for POOL --
-------------------------

-- | Check that a newly registered pool key is not in the retiring map.
rewardZeroAfterReg :: Property
rewardZeroAfterReg = withTests (fromIntegral numberOfTests) . property $ do
  tr <- fmap sourceSignalTargets
        $ forAll
        $ trace @POOL traceLen `ofLengthAtLeast` 1

  assertAll registeredPoolNotRetiring tr

  where registeredPoolNotRetiring (SourceSignalTarget
                                    { signal = c@(RegPool _)
                                    , target = p'}) =
          case cwitness c of
            KeyHashObj certWit -> let StakePools stp = getStPools p' in
                                      (  certWit ∈ dom stp
                                      && certWit ∉ dom (getRetiring p'))
            _                  -> False
        registeredPoolNotRetiring _ = True

-- | Check that if a pool retirement certificate is executed in the correct
-- epoch interval, then the pool key will be added to the retiring map but stays
-- in the set of stake pools.
poolRetireInEpoch :: Property
poolRetireInEpoch = withTests (fromIntegral numberOfTests) . property $ do
  t <- forAll (trace @POOL traceLen `ofLengthAtLeast` 1)
  let
    tr = sourceSignalTargets t
    PoolEnv s pp = _traceEnv t

  assertAll (registeredPoolRetired s pp) tr

  where registeredPoolRetired s pp (SourceSignalTarget
                                    { source = p
                                    , target = p'
                                    , signal = c@(RetirePool _ e)}) =
          case cwitness c of
            KeyHashObj certWit -> let StakePools stp  = getStPools p
                                      StakePools stp' = getStPools p'
                                      cepoch          = epochFromSlot s
                                      Epoch ce        = cepoch
                                      Epoch emax'     = _eMax pp in
                                    (  cepoch < e
                                    && e < Epoch (ce + emax')) ==>
                                    (  certWit ∈ dom stp
                                    && certWit ∈ dom stp'
                                    && Maybe.maybe False ((== e) . epochFromSlot) (stp' !? certWit))
            _                  -> False
        registeredPoolRetired _ _ _ = True
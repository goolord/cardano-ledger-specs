{-# LANGUAGE PatternSynonyms #-}

module Examples
  ( CHAINExample(..)
  , ex1
  , ex2A
  , ex2B
  , ex2C
  , ex2D
  , ex2E
  , ex2F
  , ex2G
  , ex2H
  , ex2I
  -- key pairs and example addresses
  , alicePay
  , aliceStake
  , aliceAddr
  , bobPay
  , bobStake
  , bobAddr
  , carlPay
  , carlStake
  , carlAddr
  , dariaPay
  , dariaStake
  , dariaAddr
  )
where

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (elems, empty, fromList, insert, keysSet, singleton)
import           Data.Maybe (fromMaybe)
import           Data.Sequence (fromList)
import qualified Data.Set as Set
import           Data.Word (Word64)

import           Cardano.Crypto.DSIGN (deriveVerKeyDSIGN, genKeyDSIGN)
import           Cardano.Crypto.KES (deriveVerKeyKES, genKeyKES)
import           Crypto.Random (drgNewTest, withDRG)
import           MockTypes (AVUpdate, Addr, Block, Credential, DState, EpochState, HashHeader,
                     KeyHash, KeyPair, LedgerState, NewEpochState, PPUpdate, PState, PoolDistr,
                     PoolParams, RewardAcnt, SKey, SKeyES, SnapShots, Stake, Tx, TxBody, UTxO,
                     UTxOState, Update, VKey, VKeyES, VKeyGenesis)
import           Numeric.Natural (Natural)

import           BaseTypes (Seed (..), UnitInterval, mkUnitInterval, (⭒))
import           BlockChain (pattern BHBody, pattern BHeader, pattern Block, pattern Proof,
                     ProtVer (..), TxSeq (..), bBodySize, bhHash, bhbHash, bheader, slotToSeed)
import           Coin (Coin (..))
import           Delegation.Certificates (pattern Delegate, pattern PoolDistr, pattern RegKey,
                     pattern RegPool)
import           EpochBoundary (BlocksMade (..), pattern Stake, emptySnapShots, _feeSS, _poolsSS,
                     _pstakeGo, _pstakeMark, _pstakeSet)
import           Keys (pattern Dms, pattern KeyPair, pattern SKey, pattern SKeyES, pattern VKey,
                     pattern VKeyES, pattern VKeyGenesis, hashKey, sKey, sign, signKES, vKey)
import           LedgerState (AccountState (..), pattern DPState, pattern EpochState,
                     pattern LedgerState, pattern NewEpochState, pattern RewardUpdate,
                     pattern UTxOState, deltaF, deltaR, deltaT, emptyAccount, emptyDState,
                     emptyPState, genesisCoins, genesisId, overlaySchedule, rs, _cCounters,
                     _delegations, _dms, _pParams, _ptrs, _reserves, _rewards, _stKeys, _stPools,
                     _treasury)
import           OCert (KESPeriod (..), pattern OCert)
import           PParams (PParams (..), emptyPParams)
import           Slot (Epoch (..), Slot (..))
import           TxData (pattern AddrBase, pattern Delegation, pattern KeyHashObj,
                     pattern PoolParams, Ptr (..), pattern RewardAcnt, pattern StakeKeys,
                     pattern StakePools, pattern Tx, pattern TxBody, pattern TxIn, pattern TxOut,
                     _poolCost, _poolMargin, _poolOwners, _poolPledge, _poolPubKey, _poolRAcnt,
                     _poolVrf)
import           Updates (pattern AVUpdate, Applications (..), pattern PPUpdate, Ppm (..),
                     pattern Update, emptyUpdate, emptyUpdateState)
import           UTxO (pattern UTxO, makeWitnessesVKey, txid)


type ChainState = (NewEpochState, Seed, Seed, Maybe HashHeader, Slot)

data CHAINExample = CHAINExample Slot ChainState Block ChainState


-- | Set up keys for all the actors in the examples.


mkKeyPair :: (Word64, Word64, Word64, Word64, Word64) -> (SKey, VKey)
mkKeyPair seed = fst . withDRG (drgNewTest seed) $ do
  sk <- genKeyDSIGN
  return (SKey sk, VKey $ deriveVerKeyDSIGN sk)

mkVKGen :: (Word64, Word64, Word64, Word64, Word64) -> VKeyGenesis
mkVKGen seed = fst . withDRG (drgNewTest seed) $ do
  sk <- genKeyDSIGN
  return $ VKeyGenesis $ deriveVerKeyDSIGN sk

-- | For testing purposes, generate a deterministic KES key pair given a seed.
mkKESKeyPair :: (Word64, Word64, Word64, Word64, Word64) -> (SKeyES, VKeyES)
mkKESKeyPair seed = fst . withDRG (drgNewTest seed) $ do
  sk <- genKeyKES 90
  return (SKeyES sk, VKeyES $ deriveVerKeyKES sk)

mkAddr :: (KeyPair, KeyPair) -> Addr
mkAddr (payKey, stakeKey) =
  AddrBase (KeyHashObj . hashKey $ vKey payKey) (KeyHashObj . hashKey $ vKey stakeKey)

data AllPoolKeys = AllPoolKeys
  { cold :: KeyPair
  , vrf :: KeyPair
  , hot :: (SKeyES, VKeyES)
  , hk  :: KeyHash
  } deriving (Show, Eq)

mkAllPoolKeys :: Word64 -> AllPoolKeys
mkAllPoolKeys w = AllPoolKeys (KeyPair vkCold skCold)
                              (KeyPair vkVrf skVrf)
                              (mkKESKeyPair (w, 0, 0, 0, 3))
                              (hashKey vkCold)
  where
    (skCold, vkCold) = mkKeyPair (w, 0, 0, 0, 1)
    (skVrf, vkVrf) = mkKeyPair (w, 0, 0, 0, 2)

coreNodes :: [(VKeyGenesis, AllPoolKeys)]
coreNodes = [(mkVKGen (x, 0, 0, 0, 0), mkAllPoolKeys x) | x <-[101..107]]

coreNodeVKG :: Int -> VKeyGenesis
coreNodeVKG = fst . (coreNodes !!)

coreNodeKeys :: Int -> AllPoolKeys
coreNodeKeys = snd . (coreNodes !!)

dms :: Map VKeyGenesis VKey
dms = Map.fromList [ (coreNodeVKG n, vKey $ cold $ coreNodeKeys n) | n <- [0..6]]

alicePay :: KeyPair
alicePay = KeyPair vk sk
  where (sk, vk) = mkKeyPair (0, 0, 0, 0, 0)

aliceStake :: KeyPair
aliceStake = KeyPair vk sk
  where (sk, vk) = mkKeyPair (1, 1, 1, 1, 1)

alicePool :: AllPoolKeys
alicePool = mkAllPoolKeys 1

aliceAddr :: Addr
aliceAddr = mkAddr (alicePay, aliceStake)

aliceSHK :: Credential
aliceSHK = (KeyHashObj . hashKey . vKey) aliceStake

bobPay :: KeyPair
bobPay = KeyPair vk sk
  where (sk, vk) = mkKeyPair (2, 2, 2, 2, 2)

bobStake :: KeyPair
bobStake = KeyPair vk sk
  where (sk, vk) = mkKeyPair (3, 3, 3, 3, 3)

bobAddr :: Addr
bobAddr = mkAddr (bobPay, bobStake)

bobSHK :: Credential
bobSHK = (KeyHashObj . hashKey . vKey) bobStake

aliceInitCoin :: Coin
aliceInitCoin = 10000

bobInitCoin :: Coin
bobInitCoin = 1000

alicePoolParams :: PoolParams
alicePoolParams =
  PoolParams
    { _poolPubKey = vKey $ cold alicePool
    , _poolVrf = hashKey $ vKey $ vrf alicePool
    , _poolPledge = Coin 1
    , _poolCost = Coin 5
    , _poolMargin = unsafeMkUnitInterval 0.1
    , _poolRAcnt = RewardAcnt aliceSHK
    , _poolOwners = Set.singleton $ (hashKey . vKey) aliceStake
    }


-- | Helper Functions

mkSeqNonce :: Natural -> Seed
mkSeqNonce m = foldl (\c x -> c ⭒ Nonce x) NeutralSeed [0..toInteger m]

mkBlock :: Maybe HashHeader -> AllPoolKeys -> [Tx] -> Slot
  -> Seed -> Seed -> UnitInterval -> Natural -> Block
mkBlock prev pkeys txns s enonce bnonce l kesPeriod =
  let
    (shot, vhot) = hot pkeys
    nonceSeed = (enonce ⭒ slotToSeed s) ⭒ SeedEta
    leaderSeed = (enonce ⭒ slotToSeed s) ⭒ SeedL
    bhb = BHBody
            prev
            (vKey $ cold pkeys)
            (vKey $ vrf pkeys)
            s
            bnonce
            (Proof (vKey $ vrf pkeys) nonceSeed bnonce)
            l
            (Proof (vKey $ vrf pkeys) leaderSeed l)
            (fromIntegral $ bBodySize $ (TxSeq . fromList) txns)
            (bhbHash $ TxSeq $ fromList txns)
            (OCert
              vhot
              (vKey $ cold pkeys)
              0
              (KESPeriod 0)
              (sign (sKey $ cold pkeys) (vhot, 0, KESPeriod 0))
            )
            (ProtVer 0 0 0)
    bh = BHeader bhb (Keys.signKES shot bhb kesPeriod)
  in
    Block bh (TxSeq $ fromList txns)

unsafeMkUnitInterval :: Rational -> UnitInterval
unsafeMkUnitInterval r =
  fromMaybe (error "could not construct unit interval") $ mkUnitInterval r

carlPay :: KeyPair
carlPay = KeyPair vk sk
  where (sk, vk) = mkKeyPair (4, 4, 4, 4, 4)

carlStake :: KeyPair
carlStake = KeyPair vk sk
  where (sk, vk) = mkKeyPair (5, 5, 5, 5, 5)

carlAddr :: Addr
carlAddr = mkAddr (carlPay, carlStake)


dariaPay :: KeyPair
dariaPay = KeyPair vk sk
  where (sk, vk) = mkKeyPair (6, 6, 6, 6, 6)

dariaStake :: KeyPair
dariaStake = KeyPair vk sk
  where (sk, vk) = mkKeyPair (7, 7, 7, 7, 7)

dariaAddr :: Addr
dariaAddr = mkAddr (dariaPay, dariaStake)

-- | Example 1 - apply CHAIN transition to an empty block


utxostEx1 :: UTxOState
utxostEx1 = UTxOState (UTxO Map.empty) (Coin 0) (Coin 0) emptyUpdateState

dsEx1 :: DState
dsEx1 = emptyDState { _dms = Dms dms }

psEx1 :: PState
psEx1 = emptyPState { _cCounters = Map.fromList (fmap f (Map.elems dms)) }
  where f vk = (hashKey vk, 0)

lsEx1 :: LedgerState
lsEx1 = LedgerState utxostEx1 (DPState dsEx1 psEx1) 0

ppsEx1 :: PParams
ppsEx1 = emptyPParams { _maxBBSize = 10000
                   , _maxBHSize = 10000
                   , _keyDeposit = Coin 7
                   , _poolDeposit = Coin 250
                   , _d = unsafeMkUnitInterval 0.5
                   , _activeSlotCoeff = unsafeMkUnitInterval 0.1
                   , _tau = unsafeMkUnitInterval 0.2
                   , _rho = unsafeMkUnitInterval 0.0021
                   }

esEx1 :: EpochState
esEx1 = EpochState emptyAccount emptySnapShots lsEx1 ppsEx1

initStEx1 :: ChainState
initStEx1 =
  ( NewEpochState
      (Epoch 0)
      (Nonce 0)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      esEx1
      Nothing
      (PoolDistr Map.empty)
      (Map.singleton (Slot 1) (Just $ coreNodeVKG 0))
      -- The overlay schedule has one entry, setting Core Node 1 to slot 1.
  , Nonce 0
  , Nonce 0
  , Nothing
  , Slot 0
  )

zero :: UnitInterval
zero = unsafeMkUnitInterval 0

blockEx1 :: Block
blockEx1 = mkBlock
             Nothing
             (coreNodeKeys 0)
             []
             (Slot 1)
             (Nonce 0)
             (Nonce 1)
             zero
             0

expectedStEx1 :: ChainState
expectedStEx1 =
  ( NewEpochState
      (Epoch 0)
      (Nonce 0)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      -- Note that blocks in the overlay schedule do not add to this count.
      esEx1
      Nothing
      (PoolDistr Map.empty)
      (Map.singleton (Slot 1) (Just $ coreNodeVKG 0))
  , Nonce 0 ⭒ Nonce 1
  , Nonce 0 ⭒ Nonce 1
  , Just (bhHash (bheader blockEx1))
  , Slot 1
  )

ex1 :: CHAINExample
ex1 = CHAINExample (Slot 1) initStEx1 blockEx1 expectedStEx1


-- | Example 2A - apply CHAIN transition to register stake keys and a pool


utxoEx2A :: UTxO
utxoEx2A = genesisCoins
       [ TxOut aliceAddr aliceInitCoin
       , TxOut bobAddr bobInitCoin]

ppupEx2A :: PPUpdate
ppupEx2A = PPUpdate $ Map.singleton (coreNodeVKG 0) (Set.singleton (PoolDeposit 255))

updateEx2A :: Update
updateEx2A = Update ppupEx2A (AVUpdate Map.empty)

txbodyEx2A :: TxBody
txbodyEx2A = TxBody
           (Set.fromList [TxIn genesisId 0])
           [TxOut aliceAddr (Coin 9733)]
           (fromList [ RegKey aliceSHK
           , RegKey bobSHK
           , RegPool alicePoolParams
           ])
           Map.empty
           (Coin 3)
           (Slot 10)
           updateEx2A

txEx2A :: Tx
txEx2A = Tx
          txbodyEx2A
          (makeWitnessesVKey
            txbodyEx2A
            [alicePay, aliceStake, bobStake, cold alicePool, cold $ coreNodeKeys 0])
          Map.empty

utxostEx2A :: UTxOState
utxostEx2A = UTxOState utxoEx2A (Coin 0) (Coin 0) emptyUpdateState

lsEx2A :: LedgerState
lsEx2A = LedgerState utxostEx2A (DPState dsEx1 psEx1) 0

acntEx2A :: AccountState
acntEx2A = AccountState
            { _treasury = Coin 0
            , _reserves = Coin 45*1000*1000*1000*1000*1000
            }

esEx2A :: EpochState
esEx2A = EpochState acntEx2A emptySnapShots lsEx2A ppsEx1


overlayEx2A :: Map Slot (Maybe VKeyGenesis)
overlayEx2A = overlaySchedule
                    (Epoch 0)
                    (Map.keysSet dms)
                    NeutralSeed
                    ppsEx1

initStEx2A :: ChainState
initStEx2A =
  ( NewEpochState
      (Epoch 0)
      (Nonce 0)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      esEx2A
      Nothing
      (PoolDistr Map.empty)
      overlayEx2A
  , Nonce 0
  , Nonce 0
  , Nothing
  , Slot 0
  )

blockEx2A :: Block
blockEx2A = mkBlock
             Nothing
             (coreNodeKeys 4)
             [txEx2A]
             (Slot 10)
             (Nonce 0)
             (Nonce 1)
             zero
             0

dsEx2A :: DState
dsEx2A = dsEx1
          { _ptrs = Map.fromList [ (Ptr (Slot 10) 0 0, aliceSHK)
                                 , (Ptr (Slot 10) 0 1, bobSHK) ]
          , _stKeys = StakeKeys $ Map.fromList [ (aliceSHK, Slot 10)
                                               , (bobSHK, Slot 10) ]
          , _rewards = Map.fromList [ (RewardAcnt aliceSHK, Coin 0)
                                    , (RewardAcnt bobSHK, Coin 0) ]
          }

psEx2A :: PState
psEx2A = psEx1
          { _stPools = StakePools $ Map.singleton (hk alicePool) (Slot 10)
          , _pParams = Map.singleton (hk alicePool) alicePoolParams
          , _cCounters = Map.insert (hk alicePool) 0 (_cCounters psEx1)
          }

updateStEx2A :: ( PPUpdate
               , AVUpdate
               , Map Slot Applications
               , Applications)
updateStEx2A =
  ( ppupEx2A
  , AVUpdate Map.empty
  , Map.empty
  , Applications Map.empty)

expectedLSEx2A :: LedgerState
expectedLSEx2A = LedgerState
               (UTxOState
                 (UTxO . Map.fromList $
                   [ (TxIn genesisId 1, TxOut bobAddr bobInitCoin)
                   , (TxIn (txid txbodyEx2A) 0, TxOut aliceAddr (Coin 9733))
                   ])
                 (Coin 264)
                 (Coin 3)
                 updateStEx2A)
               (DPState dsEx2A psEx2A)
               0

blockEx2AHash :: Maybe HashHeader
blockEx2AHash = Just (bhHash (bheader blockEx2A))

expectedStEx2A :: ChainState
expectedStEx2A =
  ( NewEpochState
      (Epoch 0)
      (Nonce 0)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      (EpochState acntEx2A emptySnapShots expectedLSEx2A ppsEx1)
      Nothing
      (PoolDistr Map.empty)
      overlayEx2A
  , Nonce 0 ⭒ Nonce 1
  , Nonce 0 ⭒ Nonce 1
  , blockEx2AHash
  , Slot 10
  )

ex2A :: CHAINExample
ex2A = CHAINExample (Slot 10) initStEx2A blockEx2A expectedStEx2A


-- | Example 2B - continuing on after example 2, process a block late enough
-- in the epoch in order to create a reward update.
-- The block delegates Alice's and Bob's stake to Alice's pool.

txbodyEx2B :: TxBody
txbodyEx2B = TxBody
           (Set.fromList [TxIn (txid txbodyEx2A) 0])
           [TxOut aliceAddr (Coin 9729)]
           (fromList [ Delegate $ Delegation aliceSHK (hk alicePool)
           , Delegate $ Delegation bobSHK (hk alicePool)
           ])
           Map.empty
           (Coin 4)
           (Slot 99)
           emptyUpdate

txEx2B :: Tx
txEx2B = Tx
          txbodyEx2B
          (makeWitnessesVKey txbodyEx2B [alicePay, aliceStake, bobStake, cold $ coreNodeKeys 0])
          Map.empty

blockEx2B :: Block
blockEx2B = mkBlock
             blockEx2AHash
             (coreNodeKeys 3)
             [txEx2B]
             (Slot 90)
             (Nonce 0)
             (Nonce 2)
             zero
             1

blockEx2BHash :: Maybe HashHeader
blockEx2BHash = Just (bhHash (bheader blockEx2B))

utxoEx2B :: UTxO
utxoEx2B = UTxO . Map.fromList $
                   [ (TxIn genesisId 1, TxOut bobAddr bobInitCoin)
                   , (TxIn (txid txbodyEx2B) 0, TxOut aliceAddr (Coin 9729))
                   ]

delegsEx2B :: Map Credential KeyHash
delegsEx2B = Map.fromList
              [ (aliceSHK, hk alicePool)
              , (bobSHK, hk alicePool)
              ]

dsEx2B :: DState
dsEx2B = dsEx2A { _delegations = delegsEx2B }

expectedLSEx2B :: LedgerState
expectedLSEx2B = LedgerState
               (UTxOState
                 utxoEx2B
                 (Coin 264)
                 (Coin 7)
                 updateStEx2A)
               (DPState dsEx2B psEx2A)
               0

expectedStEx2B :: ChainState
expectedStEx2B =
  ( NewEpochState
      (Epoch 0)
      (Nonce 0)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      (EpochState acntEx2A emptySnapShots expectedLSEx2B ppsEx1)
      (Just RewardUpdate { deltaT = Coin 0
                         , deltaR = Coin 0
                         , rs     = Map.empty
                         , deltaF = Coin 0
                         })
      (PoolDistr Map.empty)
      overlayEx2A
  , Nonce 0 ⭒ Nonce 1 ⭒ Nonce 2
  , Nonce 0 ⭒ Nonce 1
  , blockEx2BHash
  , Slot 90
  )

ex2B :: CHAINExample
ex2B = CHAINExample (Slot 90) expectedStEx2A blockEx2B expectedStEx2B


-- | Example 2C - continuing on after example 3, process an empty block in the next epoch
-- so that the (empty) reward update is applied and a stake snapshot is made.


blockEx2C :: Block
blockEx2C = mkBlock
             blockEx2BHash
             (coreNodeKeys 4)
             []
             (Slot 110)
             (Nonce 0)
             (Nonce 3)
             zero
             1

epoch1OSchedEx2C :: Map Slot (Maybe VKeyGenesis)
epoch1OSchedEx2C = overlaySchedule
                    (Epoch 1)
                    (Map.keysSet dms)
                    (Nonce 0 ⭒ Nonce 1)
                    ppsEx1

snapEx2C :: (Stake, Map Credential KeyHash)
snapEx2C = ( Stake ( Map.fromList [(aliceSHK, Coin 9729), (bobSHK, bobInitCoin)])
          , delegsEx2B )

snapsEx2C :: SnapShots
snapsEx2C = emptySnapShots { _pstakeMark = snapEx2C
                          , _poolsSS = Map.singleton (hk alicePool) alicePoolParams
                          , _feeSS = Coin 271
                          }

expectedLSEx2C :: LedgerState
expectedLSEx2C = LedgerState
               (UTxOState
                 utxoEx2B
                 (Coin 0)   -- TODO check that both deposits really decayed completely
                 (Coin 271) -- TODO shouldn't this pot have moved to the treasury?
                 emptyUpdateState) -- Note that the ppup is gone now
               (DPState dsEx2B psEx2A)
               0

blockEx2CHash :: Maybe HashHeader
blockEx2CHash = Just (bhHash (bheader blockEx2C))

expectedStEx2C :: ChainState
expectedStEx2C =
  ( NewEpochState
      (Epoch 1)
      (Nonce 0 ⭒ Nonce 1)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      (EpochState acntEx2A snapsEx2C expectedLSEx2C ppsEx1)
      Nothing
      (PoolDistr Map.empty)
      epoch1OSchedEx2C
  , mkSeqNonce 3
  , mkSeqNonce 3
  , blockEx2CHash
  , Slot 110
  )

ex2C :: CHAINExample
ex2C = CHAINExample (Slot 110) expectedStEx2B blockEx2C expectedStEx2C


-- | Example 2D - continuing on after example 4, process an empty block late enough
-- in the epoch in order to create a second reward update, preparing the way for
-- the first non-empty pool distribution in this running example.


blockEx2D :: Block
blockEx2D = mkBlock
             blockEx2CHash
             (coreNodeKeys 3)
             []
             (Slot 190)
             (Nonce 0 ⭒ Nonce 1)
             (Nonce 4)
             zero
             2

blockEx2DHash :: Maybe HashHeader
blockEx2DHash = Just (bhHash (bheader blockEx2D))

expectedStEx2D :: ChainState
expectedStEx2D =
  ( NewEpochState
      (Epoch 1)
      (Nonce 0 ⭒ Nonce 1)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      (EpochState acntEx2A snapsEx2C expectedLSEx2C ppsEx1)
      (Just RewardUpdate { deltaT = Coin 271
                         , deltaR = Coin 0
                         , rs     = Map.empty
                         , deltaF = Coin (-271)
                         })
      (PoolDistr Map.empty)
      epoch1OSchedEx2C
  , mkSeqNonce 4
  , mkSeqNonce 3
  , blockEx2DHash
  , Slot 190
  )

ex2D :: CHAINExample
ex2D = CHAINExample (Slot 190) expectedStEx2C blockEx2D expectedStEx2D


-- | Example 2E - continuing on after example 5, create the first non-empty pool distribution
-- by creating a block in the third epoch of this running example.


blockEx2E :: Block
blockEx2E = mkBlock
             blockEx2DHash
             (coreNodeKeys 3)
             []
             (Slot 220)
             (mkSeqNonce 3)
             (Nonce 5)
             zero
             2

epoch1OSchedEx2E :: Map Slot (Maybe VKeyGenesis)
epoch1OSchedEx2E = overlaySchedule
                    (Epoch 2)
                    (Map.keysSet dms)
                    (mkSeqNonce 3)
                    ppsEx1

snapsEx2E :: SnapShots
snapsEx2E = emptySnapShots { _pstakeMark = snapEx2C
                          , _pstakeSet = snapEx2C
                          , _poolsSS = Map.singleton (hk alicePool) alicePoolParams
                          , _feeSS = Coin 0
                          }

expectedLSEx2E :: LedgerState
expectedLSEx2E = LedgerState
               (UTxOState
                 utxoEx2B
                 (Coin 0)
                 (Coin 0)
                 emptyUpdateState)
               (DPState dsEx2B psEx2A)
               0

blockEx2EHash :: Maybe HashHeader
blockEx2EHash = Just (bhHash (bheader blockEx2E))

acntEx2E :: AccountState
acntEx2E = AccountState
            { _treasury = Coin 271
            , _reserves = Coin 45*1000*1000*1000*1000*1000
            }

expectedStEx2E :: ChainState
expectedStEx2E =
  ( NewEpochState
      (Epoch 2)
      (mkSeqNonce 3)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      (EpochState acntEx2E snapsEx2E expectedLSEx2E ppsEx1)
      Nothing
      (PoolDistr
        (Map.singleton
           (hk alicePool)
           (1, hashKey (vKey $ vrf alicePool))))
      epoch1OSchedEx2E
  , mkSeqNonce 5
  , mkSeqNonce 5
  , blockEx2EHash
  , Slot 220
  )

ex2E :: CHAINExample
ex2E = CHAINExample (Slot 220) expectedStEx2D blockEx2E expectedStEx2E


-- | Example 2F - continuing on after example 6, create a decentralized Praos block
-- (ie one not in the overlay schedule)


blockEx2F :: Block
blockEx2F = mkBlock
             blockEx2EHash
             alicePool
             []
             (Slot 295) -- odd slots open for decentralization in epoch1OSchedEx2E
             (mkSeqNonce 3)
             (Nonce 6)
             zero
             3

blockEx2FHash :: Maybe HashHeader
blockEx2FHash = Just (bhHash (bheader blockEx2F))

pdEx2F :: PoolDistr
pdEx2F = PoolDistr $ Map.singleton (hk alicePool) (1, hashKey $ vKey $ vrf alicePool)

expectedStEx2F :: ChainState
expectedStEx2F =
  ( NewEpochState
      (Epoch 2)
      (mkSeqNonce 3)
      (BlocksMade Map.empty)
      (BlocksMade $ Map.singleton (hk alicePool) 1)
      (EpochState acntEx2E snapsEx2E expectedLSEx2E ppsEx1)
      (Just RewardUpdate { deltaT = Coin 0
                         , deltaR = Coin 0
                         , rs     = Map.empty
                         , deltaF = Coin 0
                         })
      pdEx2F
      epoch1OSchedEx2E
  , mkSeqNonce 6
  , mkSeqNonce 5
  , blockEx2FHash
  , Slot 295
  )

ex2F :: CHAINExample
ex2F = CHAINExample (Slot 295) expectedStEx2E blockEx2F expectedStEx2F


-- | Example 2G - continuing on after example 7, create an empty block in the next epoch
-- to prepare the way for the first non-trivial reward update


blockEx2G :: Block
blockEx2G = mkBlock
             blockEx2FHash
             (coreNodeKeys 4)
             []
             (Slot 310)
             (mkSeqNonce 5)
             (Nonce 7)
             zero
             3

blockEx2GHash :: Maybe HashHeader
blockEx2GHash = Just (bhHash (bheader blockEx2G))

epoch1OSchedEx2G :: Map Slot (Maybe VKeyGenesis)
epoch1OSchedEx2G = overlaySchedule
                    (Epoch 3)
                    (Map.keysSet dms)
                    (mkSeqNonce 5)
                    ppsEx1

snapsEx2G :: SnapShots
snapsEx2G = snapsEx2E { _pstakeGo = snapEx2C }

expectedStEx2G :: ChainState
expectedStEx2G =
  ( NewEpochState
      (Epoch 3)
      (mkSeqNonce 5)
      (BlocksMade $ Map.singleton (hk alicePool) 1)
      (BlocksMade Map.empty)
      (EpochState acntEx2E snapsEx2G expectedLSEx2E ppsEx1)
      Nothing
      pdEx2F
      epoch1OSchedEx2G
  , mkSeqNonce 7
  , mkSeqNonce 7
  , blockEx2GHash
  , Slot 310
  )

ex2G :: CHAINExample
ex2G = CHAINExample (Slot 310) expectedStEx2F blockEx2G expectedStEx2G


-- | Example 2H - continuing on after example 8, create the first non-trivial reward update


blockEx2H :: Block
blockEx2H = mkBlock
             blockEx2GHash
             (coreNodeKeys 3)
             []
             (Slot 390)
             (mkSeqNonce 5)
             (Nonce 8)
             zero
             4

blockEx2HHash :: Maybe HashHeader
blockEx2HHash = Just (bhHash (bheader blockEx2H))

rewardsEx2H :: Map RewardAcnt Coin
rewardsEx2H = Map.fromList [ (RewardAcnt aliceSHK, Coin 82593524514)
                          , (RewardAcnt bobSHK, Coin 730001159951) ]

expectedStEx2H :: ChainState
expectedStEx2H =
  ( NewEpochState
      (Epoch 3)
      (mkSeqNonce 5)
      (BlocksMade $ Map.singleton (hk alicePool) 1)
      (BlocksMade Map.empty)
      (EpochState acntEx2E snapsEx2G expectedLSEx2E ppsEx1)
      (Just RewardUpdate { deltaT = Coin 8637405315535
                         , deltaR = Coin (-9450000000000)
                         , rs = rewardsEx2H
                         , deltaF = Coin 0
                         })
      pdEx2F
      epoch1OSchedEx2G
  , mkSeqNonce 8
  , mkSeqNonce 7
  , blockEx2HHash
  , Slot 390
  )

ex2H :: CHAINExample
ex2H = CHAINExample (Slot 390) expectedStEx2G blockEx2H expectedStEx2H


-- | Example 2I - continuing on after example 9, apply the first non-trivial reward update


blockEx2I :: Block
blockEx2I = mkBlock
              blockEx2HHash
              (coreNodeKeys 4)
              []
              (Slot 410)
              (mkSeqNonce 7)
              (Nonce 9)
              zero
              4

blockEx2IHash :: Maybe HashHeader
blockEx2IHash = Just (bhHash (bheader blockEx2I))

epoch1OSchedEx2I :: Map Slot (Maybe VKeyGenesis)
epoch1OSchedEx2I = overlaySchedule
                     (Epoch 4)
                     (Map.keysSet dms)
                     (mkSeqNonce 7)
                     ppsEx1

acntEx2I :: AccountState
acntEx2I = AccountState
            { _treasury = Coin 8637405315806
            , _reserves = Coin 44990550000000000
            }

dsEx2I :: DState
dsEx2I = dsEx2B { _rewards = rewardsEx2H }

expectedLSEx2I :: LedgerState
expectedLSEx2I = LedgerState
               (UTxOState
                 utxoEx2B
                 (Coin 0)
                 (Coin 0)
                 emptyUpdateState)
               (DPState dsEx2I psEx2A)
               0

expectedStEx2I :: ChainState
expectedStEx2I =
  ( NewEpochState
      (Epoch 4)
      (mkSeqNonce 7)
      (BlocksMade Map.empty)
      (BlocksMade Map.empty)
      (EpochState acntEx2I snapsEx2G expectedLSEx2I ppsEx1)
      Nothing
      pdEx2F
      epoch1OSchedEx2I
  , mkSeqNonce 9
  , mkSeqNonce 9
  , blockEx2IHash
  , Slot 410
  )

ex2I :: CHAINExample
ex2I = CHAINExample (Slot 410) expectedStEx2H blockEx2I expectedStEx2I

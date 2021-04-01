module Main where

import Test.Cardano.Ledger.Alonzo.Examples.Utxow (utxowExamples)
import qualified Test.Cardano.Ledger.Alonzo.Serialisation.Tripping as Tripping
import Test.Tasty

tests :: TestTree
tests =
  testGroup
    "Alonzo tests"
    [ Tripping.tests,
      utxowExamples
      --plutusScriptExamples,
      --TODO add ^^ once we can supply a proper cost model
    ]

main :: IO ()
main = defaultMain tests

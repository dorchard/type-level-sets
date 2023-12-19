{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-pre-inlining #-}

module SetSpec where

import Test.Hspec
import Data.Type.Set
import ExampleSet2

spec :: Spec
spec = do
  describe "Set tests" $ do
    it "Nub uses RHS" $ do
      fooStr    `shouldBe` "str1"
      foobarStr `shouldBe` "str2"
      barfooStr `shouldBe` "str1"
    it "Assert non-membership of a type not in a set at runtime" $ do
      barHasNat1 `shouldBe` False
    it "Union of large sets should run in reasonable time" $ do
      (r0_9 `union` r10_19) `shouldBe` (r0_9 `append` r10_19)

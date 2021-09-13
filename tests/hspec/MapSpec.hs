{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module MapSpec where

import Test.Hspec
import Examples.Example
import Examples.Example2

import Data.Type.Map

spec :: Spec
spec = do
  describe "Map tests" $
    it "Map tests" $ do
      (lookp (Var @"x") Examples.Example.foo)  `shouldBe` (2 :: Int)
      (lookp (Var @"w") Examples.Example.foo)  `shouldBe` (5 :: Int)
      (lookp (Var @"z") Examples.Example.foo)  `shouldBe` True
      (mapLength Examples.Example.foo) `shouldBe` 3
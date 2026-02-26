{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module MapSpec where

import Test.Hspec
import qualified ExampleMap as Example

import Data.Type.Map

-- Compilation test for smart constructors
myMap2 :: Map '[ "w" ':-> Int, "z" ':-> Int]
myMap2 = ext (Var :: (Var "w")) (2::Int) $ ext (Var :: (Var "z")) (4::Int) empty

spec :: Spec
spec = do
  describe "Map tests" $ do
    it "foo map lookups" $ do
      (lookp (Var @"x") Example.foo)  `shouldBe` (2 :: Int)
      (lookp (Var @"w") Example.foo)  `shouldBe` (5 :: Int)
      (lookp (Var @"z") Example.foo)  `shouldBe` True
      (mapLength Example.foo) `shouldBe` 3
    it "bar map lookups" $ do
      (lookp (Var @"y") Example.bar)  `shouldBe` (3 :: Int)
      (lookp (Var @"w") Example.bar)  `shouldBe` (1 :: Int)
      (mapLength Example.bar) `shouldBe` 2
    it "foobar union combines values correctly" $ do
      (lookp (Var @"w") Example.foobar) `shouldBe` (6 :: Int)  -- 5 + 1 combined
      (lookp (Var @"x") Example.foobar) `shouldBe` (2 :: Int)
      (lookp (Var @"y") Example.foobar) `shouldBe` (3 :: Int)
      (lookp (Var @"z") Example.foobar) `shouldBe` True
      (mapLength Example.foobar) `shouldBe` 4

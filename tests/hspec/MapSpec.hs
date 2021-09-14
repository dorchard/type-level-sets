{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module MapSpec where

import Test.Hspec
import Examples.Example
import Examples.Example2

import Data.Type.Map

-- Compilation test for smart constructors
myMap2 :: Map '[ "w" ':-> Int, "z" ':-> Int]
myMap2 = ext (Var :: (Var "w")) (2::Int) $ ext (Var :: (Var "z")) (4::Int) empty

spec :: Spec
spec = do
  describe "Map tests" $
    it "Map tests" $ do
      (lookp (Var @"x") Examples.Example.foo)  `shouldBe` (2 :: Int)
      (lookp (Var @"w") Examples.Example.foo)  `shouldBe` (5 :: Int)
      (lookp (Var @"z") Examples.Example.foo)  `shouldBe` True
      (mapLength Examples.Example.foo) `shouldBe` 3
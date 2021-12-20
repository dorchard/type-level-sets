{-# LANGUAGE DataKinds, TypeOperators, TypeFamilies, MultiParamTypeClasses #-}

module Example where

import GHC.TypeLits
import Data.Type.Map

-- Specify that key-value pairs on Ints combine to an Int
type instance Combine Int Int = Int
-- Specify that Int values for matching keys should be added
instance Combinable Int Int where
    combine x y = x + y

foo :: Map '["x" :-> Int, "z" :-> Bool, "w" :-> Int]
foo = Ext (Var :: (Var "x")) 2
    $ Ext (Var :: (Var "z")) True
    $ Ext (Var :: (Var "w")) 5
    $ Empty

foo' :: Map (AsMap '["z" :-> Bool, "x" :-> Int, "w" :-> Int])
foo' = asMap foo

bar :: Map '["y" :-> Int, "w" :-> Int]
bar = Ext (Var :: (Var "y")) 3 $
       Ext (Var :: (Var "w")) 1 $
         Empty

-- GHC can easily infer this type, so an explicit signature not necessary
-- foobar :: Map '["w" :-> Int, "x" :-> Int, "y" :-> Integer, "z" :-> Int]
foobar = foo `union` bar

foobarToFoo :: Map '["w" :-> Int, "x" :-> Int, "z" :-> Bool]
foobarToFoo = submap foobar

{-# LANGUAGE DataKinds, TypeOperators, KindSignatures, TypeFamilies, MultiParamTypeClasses #-}

import GHC.TypeLits
import Data.Type.Set (subset)
import Data.Type.Map

-- Specify that key-value pairs on Ints combine to an Int
type instance Combine Int Int = Int
-- Specify that Int values for matching keys should be added
instance Combinable Int Int where
    combine x y = x + y
                             
foo :: Map '["x" :-> Int, "z" :-> Int, "w" :-> Int]
foo = Ext (Var :: (Var "x")) 2 $
       Ext (Var :: (Var "z")) 4 $
        Ext (Var :: (Var "w")) 5 $
         Empty 


bar :: Map '["y" :-> Int, "w" :-> Int]
bar = Ext (Var :: (Var "y")) 3 $
       Ext (Var :: (Var "w")) 1 $
         Empty 

-- GHC can easily infer this type, so an explicit signature not necessary
-- foobar :: Map '["w" :-> Int, "x" :-> Int, "y" :-> Integer, "z" :-> Int]
foobar = foo `union` bar

foobarToFoo :: Map '["x" :-> Int, "z" :-> Int, "w" :-> Int]
foobarToFoo = subset foobar
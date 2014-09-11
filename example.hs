{-# LANGUAGE DataKinds, TypeOperators #-}

import Data.Type.Set

foo :: Set '["x" :-> Int, "z" :-> Int, "w" :-> Int]
foo = Ext ((Var :: (Var "x")) :-> 2) $
       Ext ((Var :: (Var "z")) :-> 4) $
        Ext ((Var :: (Var "w")) :-> 5) $
         Empty 

bar :: Set '["y" :-> Int, "w" :-> Int]
bar = Ext ((Var :: (Var "y")) :-> 3) $
       Ext ((Var :: (Var "w")) :-> 1) $
         Empty 

-- GHC can easily infer this type, so an explicit signature not necessary
-- foobar :: Set '["w" :-> Int, "x" :-> Int, "y" :-> Integer, "z" :-> Int]
foobar = foo `union` bar
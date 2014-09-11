{-# LANGUAGE DataKinds, TypeOperators, FlexibleInstances, FlexibleContexts, GADTs #-}

import Data.Type.Set

instance Nubable ((v :-> a) ': s) => Nubable ((v :-> a) ': (v :-> a) ': s) where
    nub (Ext _ (Ext x xs)) = nub (Ext x xs)

foo :: Set '["x" :-> Integer, "z" :-> Integer, "w" :-> Integer]
foo = Ext ((Var :: (Var "x")) :-> 2) $
       Ext ((Var :: (Var "z")) :-> 4) $
        Ext ((Var :: (Var "w")) :-> 5) $
         Empty 

bar :: Set '["y" :-> Integer, "w" :-> Integer]
bar = Ext ((Var :: (Var "y")) :-> 3) $
       Ext ((Var :: (Var "w")) :-> 1) $
         Empty 

foobar :: Set '["w" :-> Integer, "x" :-> Integer, "y" :-> Integer, "z" :-> Integer]
foobar = foo `union` bar
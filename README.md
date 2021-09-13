This library provides type-level sets and finite maps to Haskell, with value level counterpart, and operations for taking the union, computing
subsets/submaps, and splitting sets/maps.

This library was originally built based on "Embedding effect systems in Haskell" (Dominic Orchard, 
Tomas Petricek <http://www.cs.kent.ac.uk/~dao7/publ/haskell14-effects.pdf>) to embed effect sets. 

The following shows an example: 

	{-# LANGUAGE DataKinds, TypeOperators, TypeFamilies, MultiParamTypeClasses #-}
        import Data.Type.Map
	
        -- Specifies how to combine duplicate key-value pairs for Int values
        type instance Combine Int Int = Int
        instance Combinable Int Int where
           combine x y = x + y

        foo :: Map '["x" :-> Int, "z" :-> Bool, "w" :-> Int]
        foo = Ext (Var :: (Var "x")) 2 
            $ Ext (Var :: (Var "z")) True 
            $ Ext (Var :: (Var "w")) 5
	      Empty

        bar :: Map '["y" :-> Int, "w" :-> Int]
        bar = Ext (Var :: (Var "y")) 3
            $ Ext (Var :: (Var "w")) 1
            $ Empty 

        -- foobar :: Map '["w" :-> Int, "x" :-> Int, "y" :-> Int, "z" :-> Bool]
        foobar = foo `union` bar

The 'Map' type for 'foobar' here shows the normalised form (sorted with no duplicates).
The type signatures is commented out as it can be infered. Running the example we get:

	*Main> foobar	
	{w :-> 6, x :-> 2, y :-> 3, z :-> True}

Thus, we see that values for 'w' are added.

	 import GHC.TypeLits
	 import Data.Type.Set
	 type instance Cmp (Natural n) (Natural m) = CmpNat n m

	 data Natural (a :: Nat) where
	   Z :: Natural 0
	   S :: Natural n -> Natural (n + 1)

	 -- foo :: Set '[Natural 0, Natural 1, Natural 3]
	 foo = asSet $ Ext (S Z) (Ext (S (S (S Z))) (Ext Z Empty))

	 -- bar :: Set '[Natural 1, Natural 2]
	 bar = asSet $ Ext (S (S Z)) (Ext (S Z) (Ext (S Z) Empty))

	 -- foobar :: Set '[Natural 0, Natural 1, Natural 2, Natural 3]
	 foobar = foo `union` bar




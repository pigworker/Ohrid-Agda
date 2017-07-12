module Lec1 where

-- demo Solution

-- talk about Milner's coincidence

-- grab natural numbers from Ohrid-Nat.agda


data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

-- have a go at adding

_+N_ : Nat -> Nat -> Nat
zero +N y = y
suc x +N y = suc (x +N y)

infixr 4 _+N_

foo : Nat
foo = 5 +N 7

-- grab vectors from Ohrid-Vec.agda


data Vec (X : Set) : Nat -> Set where
  []   : Vec X 0
  _::_ : forall {n} ->
         X -> Vec X n -> Vec X (suc n)
infixr 3 _::_

head : forall {n X} -> Vec X (suc n) -> X
head (x :: xs) = x

_+V_ : forall {X n m} -> Vec X n -> Vec X m -> Vec X (n +N m)
[] +V ys = ys
(x :: xs) +V ys = x :: (xs +V ys)

-- visit Exercise and grab some bits and pieces...
-- have a go at concatenation
-- vec and vapp


vec : forall {n X} -> X -> Vec X n
vec {zero} x = []
vec {suc x} x₁ = x₁ :: vec x₁

-- HINT: you may need to override default invisibility

-- SUSPICIOUS: no specification? why not?


----------------------------------------------------------------------------
-- ??? 0.2 vectorised application                             (score: ? / 1)
----------------------------------------------------------------------------

-- implement the operator which takes the same number of functions
-- and arguments and computes the applications in corresponding
-- positions

vapp : forall {n X Y} ->
       Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp [] xs = []
vapp (f :: fs) (x :: xs) = f x :: vapp fs xs


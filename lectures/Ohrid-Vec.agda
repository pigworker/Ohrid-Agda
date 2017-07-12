module Ohrid-Vec where

open import Ohrid-Prelude
open import Ohrid-Nat

data Vec (X : Set) : Nat -> Set where
  []   : Vec X 0
  _::_ : forall {n} ->
         X -> Vec X n -> Vec X (suc n)
infixr 3 _::_


module Ohrid-Nat where

open import Ohrid-Prelude
open import Ohrid-Monoid

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero  +N n = n
suc m +N n = suc (m +N n)
infixr 3 _+N_

+Mon : Monoid Nat
+Mon = record
  { e = 0
  ; op = _+N_
  ; lunit = \ m -> refl
  ; runit = ruHelp
  ; assoc = asHelp
  } where
    ruHelp : (m : Nat) -> m +N 0 == m
    ruHelp zero     = refl
    ruHelp (suc m)  rewrite ruHelp m = refl
    asHelp : (m m' m'' : Nat) -> m +N (m' +N m'') == (m +N m') +N m''
    asHelp zero m' m'' = refl
    asHelp (suc m) m' m'' rewrite asHelp m m' m'' = refl

_*N_ : Nat -> Nat -> Nat
zero  *N n = zero
suc m *N n = m *N n +N n
infixr 4 _*N_

_N>=_ : Nat -> Nat -> Set
m      N>=  zero   =  One
zero   N>=  suc n  =  Zero
suc m  N>=  suc n  =  m N>= n

N>=Unique : (m n : Nat)(p q : m N>= n) -> p == q
N>=Unique m zero p q = refl
N>=Unique zero (suc n) () q
N>=Unique (suc m) (suc n) p q = N>=Unique m n p q

plusSucFact : (m n : Nat) -> m +N suc n == suc m +N n
plusSucFact zero n = refl
plusSucFact (suc m) n rewrite plusSucFact m n = refl

plusCommFact : (m n : Nat) -> m +N n == n +N m
plusCommFact m zero = Monoid.runit +Mon m
plusCommFact m (suc n) rewrite plusSucFact m n | plusCommFact m n = refl

sucInj : {m n : Nat} -> suc m == suc n -> m == n
sucInj refl = refl

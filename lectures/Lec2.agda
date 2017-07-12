module Lec2 where

open import Lec1

-- chop


----------------------------------------------------------------------------
-- Chopping: a weird new thing, mixing program and proof
----------------------------------------------------------------------------

-- Here's a thing you'd struggle to do in Haskell. It's really about seeing.
-- A vector of length m +N n is "Choppable" if you can show how it is given
-- by concatenating a vector of length m and a vector of length n.

data Choppable {X : Set}(m n : Nat) : Vec X (m +N n) -> Set where
  chopTo : (xs : Vec X m)(ys : Vec X n) -> Choppable m n (xs +V ys)


----------------------------------------------------------------------------
-- ??? 0.4 chop                                               (score: ? / 2)
----------------------------------------------------------------------------

chop : forall {X : Set}(m : Nat){n}(xs : Vec X (m +N n)) -> Choppable m n xs
chop zero xs = chopTo [] xs
chop (suc m) (x :: xs') with chop m xs'
chop (suc m) (x :: .(xs +V ys)) | chopTo xs ys = chopTo (x :: xs) ys

-- DON'T PANIC if you can't pattern match on the vector right away, because
-- the fact is that without looking at WHERE TO CHOP, you don't know if you
-- need to.

-- HINT You can access vectors only from the "left end", which is a big
-- clue about which number you should inspect.

-- HINT Much like in -N2 and may-take, you will probably benefit from using
-- the "with" feature to allow you to match on the outcome of a recursive
-- call.

-- DON'T PANIC if dotty things appear spontaneously in your patterns. That's
-- knowledge for free: the pattern checker is saying "you don't need to ask,
-- because I know that the only thing which goes here is such-and-such".


----------------------------------------------------------------------------
-- PROVING EQUATIONS
----------------------------------------------------------------------------

data _==_ {l}{X : Set l}(x : X) : X -> Set l {- "things equal to x" -} where
  refl : x == x  -- "there is only one way to be a thing equal to x"
  -- this does not say "there is only one way for x to be equal to x...
  -- ...or does it?"
infixr 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

{-(-}
_[=] : forall {l}{X : Set l}(x : X) -> x == x
x [=] = refl

_=[_>=_ : forall {l}{X : Set l}{y z} ->
          (x : X) -> x == y -> y == z ->
          x == z
x =[ refl >= q = q

_=<_]=_ : forall {l}{X : Set l}{y z} ->
          (x : X) -> y == x -> y == z ->
          x == z
x =< refl ]= q = q

infixr 3 _[=]
infixr 2 _=[_>=_ _=<_]=_

_=$=_ : forall {k l}{X : Set k}{Y : Set l}{f f' : X -> Y}{x x' : X} ->
          f == f' -> x == x' -> f x == f' x'
refl =$= refl = refl

infixl 1 _=$=_
{-)-}

{-(-}
-- fixity declaration for +N in the other file

assoc+N : forall x y z -> (x +N y) +N z == x +N y +N z
assoc+N zero y z = y +N z [=]
assoc+N (suc x) y z = suc [=] =$=
        (x +N y) +N z
           =[ assoc+N x y z >=
        x +N y +N z
           [=]        
{-)-}

assoc+N' : forall x y z -> (x +N y) +N z == x +N y +N z
assoc+N' zero y z = refl
assoc+N' (suc x) y z rewrite assoc+N' x y z = refl

-- or use rewrite


----------------------------------------------------------------------------
-- RECORDS
----------------------------------------------------------------------------

record Monoid (M : Set) : Set where
  field
    -- OPERATIONS ----------------------------------------
    e     : M
    op    : M -> M -> M
    -- LAWS ----------------------------------------------
    lunit : forall m -> op e m == m
    runit : forall m -> op m e == m
    assoc : forall m m' m'' ->
              op m (op m' m'') == op (op m m') m''

{-(-}
monoid+N : Monoid Nat
monoid+N = record
  { e = zero
  ; op = _+N_
  ; lunit = \ m -> refl
  ; runit = ru
  ; assoc = \ x y z -> x +N y +N z
                        =< assoc+N x y z ]=
                       (x +N y) +N z
                        [=]
  } where
  ru : forall m -> m +N 0 == m
  ru zero = refl
  ru (suc m) rewrite ru m = refl
{-)-}

{-(-}
module GRRRR where
  open Monoid monoid+N
  goo : forall x -> x == x +N 0
  goo x rewrite runit x = refl
open GRRRR
    -- how to use runit? (bring it into scope with open)
            -- rewrite and the module dance
{-)-}


------------------------------------------------------------------
-- INDEXING
------------------------------------------------------------------

{-(-}
-- some notation for working with indexed sets

_-:>_ : {I : Set}(S T : I -> Set) -> I -> Set

(S -:> T) i = S i -> T i   -- index-respecting functions

infixr 3 _-:>_

-- wrapping in the brackets means "works for all indices"

[_] : {I : Set}(X : I -> Set) -> Set
[ X ] = forall {i} -> X i
{-)-}

------------------------------------------------------------------
-- MONADS
------------------------------------------------------------------

record Monad {I}(M : (I -> Set) -> (I -> Set)) : Set1 where
  field

    return : forall {X}   -> [ X -:> M X ]
    _=<<_  : forall {X Y} -> [ X -:> M Y ] -> [ M X -:> M Y ]

  _>>=_ : forall {X Y i} -> M X i -> (forall {j} -> X j -> M Y j) -> M Y i
  mx >>= k = k =<< mx

  _<=<_ : forall {X Y Z : (I -> Set)} ->
            [ Y -:> M Z ] -> [ X -:> M Y ] -> [ X -:> M Z ]
  (f <=< g) x = f =<< g x
  -- laws?


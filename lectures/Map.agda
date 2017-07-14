module Map where

data Maybe (X : Set) : Set where
  no : Maybe X
  yes : X -> Maybe X

data Two : Set where tt ff : Two

isYes : forall {X} -> Maybe X -> Two
isYes no = ff
isYes _  = tt

data Map (X : Set) : Two -> Set where
  [] : Map X tt
  _,-_ : forall {b}(mx : Maybe X) -> Map X (isYes mx) -> Map X b
infixr 4 _,-_

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

MAP : Set -> Set
MAP X = Map X tt

singleton : forall {X b} -> Nat -> X -> Map X b
singleton zero    x = yes x ,- []
singleton (suc n) x = no ,- singleton n x

ttify : forall {X b} -> Map X b -> Map X tt
ttify []         = []
ttify (mx ,- xm) = mx ,- xm

insert : forall {X b} -> Nat -> X -> Map X b -> Map X b
insert n       x []         = singleton n x
insert zero    x (mx ,- xm) = yes x ,- ttify xm
insert (suc n) x (mx ,- xm) = mx ,- insert n x xm

delete : forall {X b} -> Nat -> Map X b -> MAP X
delete n [] = []
delete zero (no ,- mx) = no ,- mx
delete zero (yes x ,- []) = []
delete zero (yes x ,- mx ,- xm) = no ,- mx ,- xm
delete (suc n) (no ,- xm) with delete n xm
delete (suc n) (no ,- xm) | [] = []
delete (suc n) (no ,- xm) | mx ,- xm' = no ,- mx ,- xm'
delete (suc n) (yes x ,- mx) = yes x ,- delete n mx

lookup : forall {X b} -> Nat -> Map X b -> Maybe X
lookup n [] = no
lookup zero (mx ,- xm) = mx
lookup (suc n) (mx ,- xm) = lookup n xm

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x

sym :  forall {l}{X : Set l}{x y : X} -> x == y -> y == x
sym refl = refl

trans : forall {l}{X : Set l}{x y z : X} -> x == y -> y == z -> x == z
trans refl q = q

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixr 4 _,_

firstYes : forall {X b}(mx : Maybe X)(xm : Map X (isYes mx)) ->
           Sg Nat \ n -> Sg X \ x ->
           lookup {b = b} n (mx ,- xm) == yes x
firstYes no (mx ,- xm) with firstYes mx xm
... | n , x , q = suc n , x , q
firstYes (yes x) xm = zero , (x , refl)

extMap : forall {X b}(xm : Map X b)(ym : Map X b) ->
        (forall n -> lookup n xm == lookup n ym) ->
        xm == ym
extMap [] [] q = refl
extMap [] (mx ,- ym) q with firstYes mx ym
... | n , x , w with trans (q n) w
extMap [] (mx ,- ym) q | n , x , w | ()
extMap (mx ,- xm) [] q with firstYes mx xm
... | n , x , w with trans (sym (q n)) w
extMap (mx ,- xm) [] q | n , x , w | ()
extMap (mx ,- xm) (my ,- ym) q with q zero
extMap (mx ,- xm) (.mx ,- ym) q | refl with extMap xm ym \ n -> q (suc n)
extMap (mx ,- xm) (.mx ,- .xm) q | refl | refl = refl


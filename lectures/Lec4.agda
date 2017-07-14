module Lec4 where

open import Ohrid-Prelude

record Stream (X : Set) : Set where
  coinductive
  constructor _,-_
  field
    head : X
    tail : Stream X
open Stream public

zip : forall {X Y} -> Stream X -> Stream Y -> Stream (X * Y)
head (zip xs ys) = (head xs) , (head ys)
tail (zip xs ys) = zip (tail xs) (tail ys)

unzip : forall {X Y} -> Stream (X * Y) -> Stream X * Stream Y
head (fst (unzip xys)) = fst (head xys)
tail (fst (unzip xys)) = fst (unzip (tail xys))
head (snd (unzip xys)) = snd (head xys)
tail (snd (unzip xys)) = snd (unzip (tail xys))

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

record Colist (X : Set) : Set where
  coinductive
  field
    force : Maybe (X * Colist X)
open Colist public

_+C_ : forall {X} -> Colist X -> Colist X -> Colist X
force (xs +C ys) with (force xs)
force (xs +C ys) | yes (x , xs') = yes (x , (xs' +C ys))
force (xs +C ys) | no = force ys

-- Demux puzzle
data Demux' (A B : Set) : Set
record Demux (A B : Set) : Set where
  coinductive
  constructor mux
  field
    xum : Demux' A B
open Demux
data Demux' A B where
  stick : A -> Demux' A B -> Demux' A B
  twist : B -> Demux  B A -> Demux' A B

lefts   : forall {A B} -> Demux  A B -> Stream A
lefts'  : forall {A B} -> Demux' A B -> Stream A
rights  : forall {A B} -> Demux  A B -> Stream B
rights' : forall {A B} -> Demux' A B -> Stream B
lefts abd = lefts' (xum abd)
head (lefts' (stick a abd')) = a
tail (lefts' (stick a abd')) = lefts' abd'
lefts' (twist b bad) = rights bad
rights abd = rights' (xum abd)
rights' (stick a abd') = rights' abd'
head (rights' (twist b bad)) = b
tail (rights' (twist b bad)) = lefts bad

demux : forall {A B} -> Demux A B -> Stream A * Stream B
fst (demux abd) = lefts abd
snd (demux abd) = rights abd

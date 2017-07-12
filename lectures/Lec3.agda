module Lec3 where

open import Ohrid-Prelude
open import Ohrid-Nat
open import Ohrid-Vec
open import Ohrid-Indexed

----------------------------------------------------------------------------
-- Vector stuff from earlier lectures
----------------------------------------------------------------------------

_+V_ : forall {X n m} -> Vec X n -> Vec X m -> Vec X (n +N m)
[] +V ys = ys
(x :: xs) +V ys = x :: (xs +V ys)

vec : forall {n X} -> X -> Vec X n
vec {zero} x = []
vec {suc n} x = x :: vec x

vapp : forall {n X Y} ->
       Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp [] xs = []
vapp (f :: fs) (x :: xs) = f x :: vapp fs xs

_<*>_ = vapp
infixl 2 _<*>_


---------------------------------------------------------------------------
--                                                                       --
-- EPISODE 1: BOXES                                           [5 marks]  --
--                                                                       --
---------------------------------------------------------------------------


data Box (X : Nat * Nat -> Set)(wh : Nat * Nat) : Set where
--        ^basic-tile             width^   ^height

  tile : X wh -> Box X wh
--       a basic tile is a tiling

  leri : (wl : Nat)   (bl : Box X (wl , snd wh))
         (wr : Nat)   (br : Box X (wr , snd wh))
         -> wl +N wr == fst wh -> Box X wh
-- combine "left" and "right" tilings the same height
-- to make a tiling with their total width

  tobo : (ht : Nat)   (bt : Box X (fst wh , ht))
         (hb : Nat)   (bb : Box X (fst wh , hb))
         -> ht +N hb == snd wh -> Box X wh
-- combine "top" and "bottom" tilings the same width
-- to make a tiling with their total height

boxMonadIx : MonadIx Box
boxMonadIx = record { retIx = tile ; extendIx = go } where
  go : {X Y : Nat * Nat → Set} ->
                [ X -:> Box Y ] -> [ Box X -:> Box Y ]
  go k (tile x) = k x
  go k (leri wl le wr ri q) = leri wl (go k le) wr (go k ri) q
  go k (tobo ht to hb bo q) = tobo ht (go k to) hb (go k bo) q


---------------------------------------------------------------------------
-- PASTE KITS AND MATRICES                                               --
---------------------------------------------------------------------------

-- A "paste kit" for sized stuff is whatever you need to combine stuff
-- left-to-right and top-to-bottom

record PasteKit (X : Nat * Nat -> Set) : Set where  -- say ALGEBRA
  field
    leriPaste : (wl wr : Nat){h : Nat} ->
                X (wl , h) -> X (wr , h) -> X ((wl +N wr) , h)
    toboPaste : {w : Nat}(ht hb : Nat) ->
                X (w , ht) -> X (w , hb) -> X (w , (ht +N hb))

-- Show that a PasteKit is just what you need to turn a tiling of
-- stuff into some stuff. (1 mark)

pasteBox : {X : Nat * Nat -> Set} -> PasteKit X -> [ Box X -:> X ]
pasteBox {X} pk = go where
  open PasteKit pk -- brings leriPaste and toboPaste into scope
  go : [ Box X -:> X ]
  go (tile x) = x
  go (leri wl bl wr br refl) = leriPaste wl wr (go bl) (go br)
  go (tobo ht bt hb bb refl) = toboPaste ht hb (go bt) (go bb)

-- If you were wondering what any of this had to do with part 0, here we
-- go...

Matrix : Set -> Nat * Nat -> Set
Matrix C (w , h) = Vec (Vec C w) h
-- matrices are "sized stuff", represented as a vector the right height
-- of rows which are vectors the right width of some sort of unit "cell".

{-+}
matrixPasteKit : {C : Set} -> PasteKit (Matrix C)
matrixPasteKit = record
  { leriPaste = \ wl wr ml mr -> {!!}
  ; toboPaste = \ ht hb mt mb -> {!!}
  }
{+-}

---------------------------------------------------------------------------
-- INTERLUDE: TESTING WITH TEXT                                          --
---------------------------------------------------------------------------

{-+}
-- Turn a list into a vector, either by truncating or padding with
-- a given dummy element.
paddy : {X : Set} -> X -> List X -> {n : Nat} -> Vec X n
paddy _ _         {zero}   = []
paddy x []        {suc n}  = x :: paddy x [] {n}
paddy x (y :: ys) {suc n}  = y :: paddy x ys {n}

-- Use that to make vectors of characters from strings, padding with space.
[-_-] : String -> {n : Nat} -> Vec Char n
[- s -] = paddy ' ' (primStringToList s)

-- Here are some.
mat43-1 : Matrix Char (4 , 3)
mat43-1 = [- "post" -] :: [- "cake" -] :: [- "flop" -] :: []

mat43-2 : Matrix Char (4 , 3)
mat43-2 = [- "horn" -] :: [- "walk" -] :: [- "ping" -] :: []

mat22 : Matrix Char (2 , 2)
mat22 = [- "go" -] :: [- "do" -] :: []

mat62 : Matrix Char (6 , 2)
mat62 = [- "getter" -] :: [- "gooder" -] :: []

-- Put them together as a tiling.
myTiling : Box (Matrix Char) (8 , 5)
myTiling = tobo 3 (leri 4 (tile mat43-1) 4 (tile mat43-2) refl)
                2 (leri 2 (tile mat22) 6 (tile mat62) refl) refl

-- Paste all the pieces and see what you get!
myText : Matrix Char (8 , 5)
myText = pasteBox matrixPasteKit myTiling
{+-}


---------------------------------------------------------------------------
--                                                                       --
-- EPISODE 2: CUT KITS AND MATRICES                           [2 marks]  --
--                                                                       --
---------------------------------------------------------------------------

-- A "cut kit" for sized stuff is whatever you need to cut stuff into
-- smaller pieces: left-and-right pieces, or top-and-bottom pieces.

record CutKit (X : Nat * Nat -> Set) : Set where
  field
    cutLR : (w h wl wr : Nat) -> wl +N wr == w ->
            X (w , h) -> X (wl , h) * X (wr , h)
    cutTB : (w h ht hb : Nat) -> ht +N hb == h ->
            X (w , h) -> X (w , ht) * X (w , hb)



---------------------------------------------------------------------------
-- HOLES                                                                 --
---------------------------------------------------------------------------

-- We might want to make sure that, whatever other basic tiles are in play,
-- we can have tiles which are "missing", as if we had cut rectangular
-- holes in a piece of paper.

data HoleOr (X : Nat * Nat -> Set)(wh : Nat * Nat) : Set where
  hole  : HoleOr X wh
  stuff : X wh -> HoleOr X wh

-- A HoleOr X is (you guessed it) either a hole or an X.

-- Show that if X has a CutKit, so has HoleOr X. What do you get when you
-- cut up a hole? (1 mark)

{-+}
holeCutKit : {X : Nat * Nat -> Set} -> CutKit X -> CutKit (HoleOr X)
holeCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) -> wl +N wr == w ->
        HoleOr X (w , h) -> HoleOr X (wl , h) * HoleOr X (wr , h)
  clr w h wl wr wq y = {!!}
  ctb : (w h ht hb : Nat) -> ht +N hb == h ->
        HoleOr X (w , h) -> HoleOr X (w , ht) * HoleOr X (w , hb)
  ctb w h ht hb hq y = {!!}
{+-}

---------------------------------------------------------------------------
-- A CUTKIT FOR BOXES                                                    --
---------------------------------------------------------------------------

-- going on a raid to the Exercise file will be useful at some point

{-+}
boxCutKit : {X : Nat * Nat -> Set} -> CutKit X -> CutKit (Box X)
boxCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) -> wl +N wr == w ->
        Box X (w , h) -> Box X (wl , h) * Box X (wr , h)
  clr w h wl wr wq b = {!!}
  ctb : (w h ht hb : Nat) -> ht +N hb == h ->
        Box X (w , h) -> Box X (w , ht) * Box X (w , hb)
  ctb w h ht hb hq b = {!!}
{+-}


---------------------------------------------------------------------------
-- MASK                                                                  --
---------------------------------------------------------------------------

-- We can now implement a general purpose superimposition operator.
-- The idea is that a tiling of X-tiles (which might, e.g., have holes)
-- is in front and a tiling of Y-tiles is behind it.
-- If have a CutKit for Y, and a function that combines X-tiles and
-- Y-tilings to make Z-tilings, you can cut up the back layer into
-- regions which are masked by the tiles in the front layer, then
-- combine them. E.g., if the front layer is made of (HoleOr Y)
-- and the back is made of Y, then you can arrange to fill the holes
-- in the front with the regions from the back that you would be able
-- to see through the holes. (2 marks)

{-+}
mask : {X Y Z : Nat * Nat -> Set} -> CutKit Y ->
       [ X -:> Box Y -:> Box Z ] ->
                     [
       {- front -}     Box X -:>
       {- back  -}     Box Y -:>
       {- combined -}  Box Z ]
mask {X}{Y}{Z} ck m = go where
  open CutKit (boxCutKit ck)
  go : [ Box X -:> Box Y -:> Box Z ]
  go xb yb = {!!}

overlay : {X : Nat * Nat -> Set} -> CutKit X ->
          [ Box (HoleOr X) -:> Box (HoleOr X) -:> Box (HoleOr X) ]
overlay ck = {!!}
{+-}

---------------------------------------------------------------------
-- if time permits
---------------------------------------------------------------------

record Partition (P : Set) : Set1 where
  field
    Cuts    : P -> Set
    pieces  : {p : P} -> Cuts p -> List P

All : {X : Set} -> (X -> Set) -> List X -> Set
All P []        = One
All P (x :: xs) = P x * All P xs


module SPACEMONAD {P}(Part : Partition P) where

  open Partition Part

  data Interior (X : P -> Set)(p : P) : Set where

    <_>  :    X p ->
            ---------------------
              Interior X p

    _8><_ :   (c : Cuts p) ->
              All (Interior X) (pieces c) ->
            --------------------------------
              Interior X p

  infixr 4 _8><_

  inlay : forall {X Y} ->
            [ X -:> Interior Y ] ->
            [ Interior X -:> Interior Y ]
  inlays : forall {X Y} -> [ X -:> Interior Y ] ->
            [ All (Interior X) -:> All (Interior Y) ]

  inlay x2yI < x >        = x2yI x
  inlay x2yI (c 8>< xIs)  = c 8>< inlays x2yI xIs

  inlays x2yI {[]}      <>          = <>
  inlays x2yI {p :: ps} (xI , xIs)  = inlay x2yI xI , inlays x2yI xIs

  spaceMonadIx : MonadIx Interior
  spaceMonadIx = record { retIx = <_> ; extendIx = inlay } where

  open MonadIx spaceMonadIx

module BST where

  _<=_ : Nat -> Nat -> Set
  zero   <= y     = One
  suc x <= zero   = Zero
  suc x <= suc y  = x <= y

{-+}
  cmp : (x y : Nat) -> (x <= y) + (y <= x)
  cmp x y = ?
+-}

  data Bound : Set where
    bot : Bound
    val : Nat -> Bound
    top : Bound

  Order : Bound * Bound -> Set
  Order (bot   , _)     = One
  Order (val x , val y) = x <= y
  Order (_     , top)   = One
  Order (_     , _)     = Zero

{-+}
  Search : Partition (Bound * Bound)
  Search = record { Cuts = \ _ -> ? ; pieces = \ { {l , u} k -> ? } }
{+-}

{-+}
  open SPACEMONAD Search

  Tree : (Bound * Bound) -> Set
  Tree = Interior Order

  Interval : (Bound * Bound) -> Set
  Interval (l , u) = Sg Nat \ k -> Order (l , val k) * Order (val k , u)
{+-}

{-+}
  insert : [ Interval -:> Tree -:> Tree ]
  insert (k , lk , ku) t = ?
{+-}

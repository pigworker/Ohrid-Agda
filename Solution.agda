module Solution where

open import Ohrid-Prelude
open import Ohrid-Nat
open import Ohrid-Vec
open import Ohrid-Indexed
open import Ohrid-Monoid
open import WindowsSetup

---------------------------------------------------------------------------
-- BOXES (5 marks)                                                       --
---------------------------------------------------------------------------

-- Boxes are sized rectangular tilings which fit together precisely.
-- They allow us to talk about the use of 2D space, e.g., on a screen.

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


---------------------------------------------------------------------------
-- MONADIC STRUCTURE                                                     --
---------------------------------------------------------------------------

-- Show that Box has the MonadIx structure:
--   every X-tile can be made into an X-tiling;
--   if you can turn X-tiles into Y-tilings,
--     then you can turn X-tilings into Y-tilings.

boxMonadIx : MonadIx Box
boxMonadIx = record { retIx = tile ; extendIx = boxExtendIx } where
  boxExtendIx : {X Y : Nat * Nat → Set} ->
                [ X -:> Box Y ] -> [ Box X -:> Box Y ]
  boxExtendIx k (tile x) = k x
  boxExtendIx k (leri wl bl wr br q) =
    leri wl (boxExtendIx k bl) wr (boxExtendIx k br) q
  boxExtendIx k (tobo ht bt hb bb q) =
    tobo ht (boxExtendIx k bt) hb (boxExtendIx k bb) q

boxMonadIxLaws : MonadIxLaws boxMonadIx
boxMonadIxLaws = record
  { lunit = \ f p -> refl
  ; runit = \ f p -> ru (f p)
  ; assoc = \ f g h p -> as g h (f p)
  } where
  open MonadIx boxMonadIx
  ru : {P : Nat * Nat -> Set} {i : Nat * Nat}
        (p : Box P i) ->
        extendIx retIx p == p
  ru (tile x) = refl
  ru (leri wl bl wr br q) rewrite ru bl | ru br = refl
  ru (tobo ht bt hb bb q) rewrite ru bt | ru bb = refl
  as : {P Q R : Nat * Nat -> Set} (f : [ P -:> Box Q ])
       (g : [ Q -:> Box R ]) {i : Nat * Nat}
       (p : Box P i) ->
       extendIx g (extendIx f p) ==
       extendIx (f -Ix- g) p
  as f g (tile x) = refl
  as f g (leri wl bl wr br q) rewrite as f g bl | as f g br = refl
  as f g (tobo ht bt hb bb q) rewrite as f g bt | as f g bb = refl


---------------------------------------------------------------------------
-- PASTE KITS AND MATRICES                                               --
---------------------------------------------------------------------------

-- A "paste kit" for sized stuff is whatever you need to combine stuff
-- left-to-right and top-to-bottom

record PasteKit (X : Nat * Nat -> Set) : Set where
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
  go (leri wl lb wr rb refl) = leriPaste wl wr (go lb) (go rb)
  go (tobo ht tb hb bb refl) = toboPaste ht hb (go tb) (go bb)

-- If you were wondering what any of this had to do with part 1, here we
-- go...

Matrix : Set -> Nat * Nat -> Set
Matrix C (w , h) = Vec (Vec C w) h
-- matrices are "sized stuff", represented as a vector the right height
-- of rows which are vectors the right width of some sort of unit "cell".

-- Pasting in any useful equipment you built in earlier exercises
-- (yes, it was all done for a reason!), give matrices their PasteKit.
-- (1 mark)

{- from Ex1 -}
_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
[]        +V  ys  = ys
(x :: xs) +V  ys  = x :: xs +V ys
infixr 3 _+V_

data Choppable {X : Set}(m n : Nat) : Vec X (m +N n) -> Set where
  chopTo : (xs : Vec X m)(ys : Vec X n) -> Choppable m n (xs +V ys)

chop : {X : Set}(m n : Nat)(xs : Vec X (m +N n)) -> Choppable m n xs
chop zero    n xs                 = chopTo [] xs
chop (suc m) n (x :: xs)          with chop m n xs
chop (suc m) n (x :: .(xs +V ys)) | chopTo xs ys = chopTo (x :: xs) ys

vec : forall {n X} -> X -> Vec X n
vec {zero}  x = []
vec {suc n} x = x :: vec {n} x

vapp : forall {n X Y} ->
       Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp []        []        = []
vapp (f :: fs) (x :: xs) = f x :: vapp fs xs

vmap : forall {n X Y} ->
       (X -> Y) -> Vec X n -> Vec Y n
vmap f xs = vapp (vec f) xs

vzip : forall {n X Y} ->
       Vec X n -> Vec Y n -> Vec (X * Y) n
vzip xs ys = vapp (vmap _,_ xs) ys

data UnZipped {X Y n} : Vec (X * Y) n -> Set where
  unzipped : (xs : Vec X n)(ys : Vec Y n) -> UnZipped (vzip xs ys)
  
unzip : forall {X Y n}(xys : Vec (X * Y) n) -> UnZipped xys
unzip []          = unzipped [] []
unzip (xy :: xys) with unzip xys
unzip ((x , y) :: .(vapp (vmap _,_ xs) ys)) | unzipped xs ys =
  unzipped (x :: xs) (y :: ys)

vunzip : forall {X Y n}(xys : Vec (X * Y) n) -> Vec X n * Vec Y n
vunzip xys with unzip xys
vunzip .(vapp (vapp (vec _,_) xs) ys) | unzipped xs ys = xs , ys

vappidlem : forall {X n}(xs : Vec X n) -> vapp (vec id) xs == xs
vappidlem []        = refl
vappidlem (x :: xs) rewrite vappidlem xs = refl

vappcomplem : forall {X Y Z n} ->
              (fs : Vec (Y -> Z) n)(gs : Vec (X -> Y) n)(xs : Vec X n) ->
              vapp (vapp (vapp (vec _o_) fs) gs) xs == vapp fs (vapp gs xs)
vappcomplem []        []        []        = refl
vappcomplem (f :: fs) (g :: gs) (x :: xs) rewrite vappcomplem fs gs xs = refl

vecvapplem : forall {X Y n}(f : X -> Y)(x : X) ->
             vec (f x) == vapp {n} (vec f) (vec x)
vecvapplem {n = zero}  f x = refl
vecvapplem {n = suc n} f x rewrite vecvapplem {n = n} f x = refl

vapplem : forall {X Y n}(fs : Vec (X -> Y) n) -> (x : X) ->
      vapp fs (vec x) == vapp (vec (\ f -> f x)) fs
vapplem []        x = refl
vapplem (f :: fs) x rewrite vapplem fs x = refl

-- applicative

record Applicative (T : Set -> Set) : Set₁ where
  field
    pure         : forall {X} -> X -> T X
    _<*>_        : forall {X Y} -> T (X -> Y) -> T X -> T Y
    identity     : forall {X}(v : T X) -> pure id <*> v == v
    composition  : forall {X Y Z}(u : T (Y -> Z))(v : T (X -> Y))(w : T X) ->
                   pure _o_ <*> u <*> v <*> w == u <*> (v <*> w)
    homomorphism : forall {X Y}(f : X -> Y)(x : X) ->
                   pure (f x) == pure f <*> pure x
    interchange  : forall {X Y}(u : T (X -> Y))(y : X) ->
                   u <*> pure y == pure (\ f -> f y) <*> u
  infixl 10 _<*>_

-- vecs are applicative

VecApp : forall n -> Applicative \X -> Vec X n
VecApp n = record
  { pure         = vec
  ; _<*>_        = vapp
  ; identity     = vappidlem
  ; composition  = vappcomplem
  ; homomorphism = vecvapplem
  ; interchange  = vapplem
  }  

{- end paste from Ex1 & 2 -}

matrixPasteKit : {C : Set} -> PasteKit (Matrix C)
matrixPasteKit = record
  { leriPaste = \ _ _ ls rs -> vapp (vapp (vec _+V_) ls) rs
  ; toboPaste = \ _ _ -> _+V_
  }


---------------------------------------------------------------------------
-- INTERLUDE: TESTING WITH TEXT                                          --
---------------------------------------------------------------------------

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


---------------------------------------------------------------------------
-- CUT KITS, MATRICES                                                    --
---------------------------------------------------------------------------

-- A "cut kit" for sized stuff is whatever you need to cut stuff into
-- smaller pieces: left-and-right pieces, or top-and-bottom pieces.

record CutKit (X : Nat * Nat -> Set) : Set where
  field
    cutLR : (w h wl wr : Nat) -> wl +N wr == w ->
            X (w , h) -> X (wl , h) * X (wr , h)
    cutTB : (w h ht hb : Nat) -> ht +N hb == h ->
            X (w , h) -> X (w , ht) * X (w , hb)

-- Equip matrices with their CutKit. (1 mark)

vchop : forall {X} m {n} -> Vec X (m +N n) -> Vec X m * Vec X n
vchop m xs with chop m _ xs
vchop m .(xs +V ys) | chopTo xs ys = xs , ys

open module _Foo {n : Nat} = Applicative (VecApp n)

matrixCutKit : {C : Set} -> CutKit (Matrix C)
matrixCutKit {C} = record {
    cutLR = \ {.(wl +N wr) h wl wr refl css ->
            vunzip (vec (vchop wl) <*> css)} ;
    cutTB = \ {w .(ht +N hb) ht hb refl -> vchop ht } }


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

holeCutKit : {X : Nat * Nat -> Set} -> CutKit X -> CutKit (HoleOr X)
holeCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) -> wl +N wr == w ->
        HoleOr X (w , h) -> HoleOr X (wl , h) * HoleOr X (wr , h)
  clr w h wl wr wq hole = hole , hole
  clr w h wl wr wq (stuff x) with cutLR w h wl wr wq x
  clr w h wl wr wq (stuff x) | xl , xr = stuff xl , stuff xr
  ctb : (w h ht hb : Nat) -> ht +N hb == h ->
        HoleOr X (w , h) -> HoleOr X (w , ht) * HoleOr X (w , hb)
  ctb w h ht hb hq hole = hole , hole
  ctb w h ht hb hq (stuff x) with cutTB w h ht hb hq x
  ctb w h ht hb hq (stuff x) | xt , xb = stuff xt , stuff xb


---------------------------------------------------------------------------
-- A BIT OF FUN                                                          --
---------------------------------------------------------------------------

-- Show that you can turn holes into spaces.

holeSpace : [ HoleOr (Matrix Char) -:> Matrix Char ]
holeSpace hole = vec (vec ' ')
holeSpace (stuff x) = x

-- Show how to render a tiling made of text or holes as text.

renderHoleOrText : [ Box (HoleOr (Matrix Char)) -:> Matrix Char ]
renderHoleOrText = pasteBox matrixPasteKit o mapIx holeSpace where
  open FunctorIx (monadFunctorIx boxMonadIx)

-- Make a test example and see!

myTest : Matrix Char (8 , 6)
myTest = renderHoleOrText
  (leri 3 (tobo 4 (tile (stuff (vec (vec '*')))) 2 (tile hole) refl)
        5 (tobo 2 (tile hole) 4 (tile (stuff (vec (vec '=')))) refl) refl)


---------------------------------------------------------------------------
-- CUTTING UP BOXES (5 marks)                                            --
---------------------------------------------------------------------------

-- Previously...
-- ... we established what it is to be a CutKit, and we built CutKits
-- for some sorts of basic tile. Now we need to build the CutKit for
-- Box. Let's think about what that involves for a moment. We're going
-- to need a CutKit for basic tiles to stand a chance. But how do we
-- cut compound tiles?
--
-- Suppose we're writing cutLR, and we have some
--   cq : cwl + cwr == w   -- the "cut widths" equation
-- telling us where we want to make the cut in something of width w.
--
--             v
--    +--------:------+
--    |        :      |
--    |        :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
-- The tricky part is when the box we're cutting here is built with
--   leri bwl bl bwr br bq
-- where
--   bq : bwl + bwr == w   -- the "box widths" equation
--
-- There are three possible situations, all of which you must detect
-- and handle.
--
-- (i) you hit the sweet spot...
--
--             v
--    +--bwl---+-bwr--+
--    |        |      |
--    |        |      |
--    +--cwl---+-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...where the box is already divided in the place where the cut
--     has to go. Happy days.
--
-- (ii) you're cutting to the left of the join...
--
--             v
--    +--bwl-----+bwr-+
--    |        : |    |
--    |        : |    |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the left box in the correct place. You
--     will need some evidence about widths to do that. And then you'll
--     the have three pieces you can see in my diagram, so to complete
--     the cut, you will need to put two of those pieces together, which
--     will take more evidence.
--
-- (iii) you're cutting to the right of the join...
--
--             v
--    +--bwl-+--bwr---+
--    |      | :      |
--    |      | :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the right box in the correct place, and
--     reassemble the bits.
--
-- HINT: THE FIRST THREE MARKS IN THIS EPISODE COME FROM ONE PROBLEM.
-- TREAT THEM AS A WHOLE.


---------------------------------------------------------------------------
-- COMPARING THE CUT POSITION                                            --
---------------------------------------------------------------------------

data CutCompare (x x' y y' n : Nat) : Set where
  cutLt : (d : Nat) -> x +N suc d == y -> suc d +N y' == x' ->
    CutCompare x x' y y' n
  cutEq : x == y -> x' == y' ->
    CutCompare x x' y y' n
  cutGt : (d : Nat) -> y +N suc d == x -> suc d +N x' == y' ->
    CutCompare x x' y y' n
  -- Give three constructors for this type which characterize the three
  -- possibilities described above whenever
  --   x + x' == n   and   y + y' == n
  -- (E.g., take n to be w, x and x' to be cwl and cwr, y and y' to be
  -- bwl and bwr. But later, you'll need to do use the same tool for
  -- heights.)
  --
  -- You will need to investigate what evidence must be packaged in each
  -- situation. On the one hand, you need to be able to *generate* the
  -- evidence, with cutCompare, below. On the other hand, the evidence
  -- must be *useful* when you come to write boxCutKit, further below.
  -- Don't expect to know what to put here from the get-go. Figure it
  -- out by discovering what you *need*.
  --
  -- (1 mark)

-- Show that whenever you have two ways to express the same n as a sum,
-- you can always deliver the CutCompare evidence. (1 mark)

cutCompare : (x x' y y' n : Nat) -> x +N x' == n -> y +N y' == n ->
             CutCompare x x' y y' n
cutCompare zero .n zero .n n refl refl
  = cutEq refl refl
cutCompare zero .(suc (y +N y')) (suc y) y' .(suc (y +N y')) refl refl
  = cutLt y refl refl
cutCompare (suc x) x' zero .(suc (x +N x')) .(suc (x +N x')) refl refl
  = cutGt x refl refl
cutCompare (suc x) x' (suc y) y' zero () ()
cutCompare (suc x) x' (suc y) y' (suc n) xq yq
  with cutCompare x x' y y' n (sucInj xq) (sucInj yq) 
cutCompare (suc x) x' (suc .(x +N suc d)) y' (suc n) xq yq | cutLt d refl bq
  = cutLt d refl bq -- cutLt d refl bq
cutCompare (suc x) x' (suc .x) y' (suc n) xq yq | cutEq refl bq = cutEq refl bq -- cutEq refl bq
cutCompare (suc .(y +N suc d)) x' (suc y) y' (suc n) xq yq | cutGt d refl bq = cutGt d refl bq -- cutGt d refl bq
-- cutCompare x x' y y' n xq yq = {!!}


---------------------------------------------------------------------------
-- A CUTKIT FOR BOXES                                                    --
---------------------------------------------------------------------------

-- Now, show that you can construct a CutKit for Box X, given a CutKit
-- for X. There will be key points where you get stuck for want of crucial
-- information. The purpose of CutCompare is to *describe* that
-- information. The purpose of cutCompare is to *compute* that information.
-- Note that cutLR and cutTB will work out very similarly, just exchanging
-- the roles of width and height.
-- (1 mark)

boxCutKit : {X : Nat * Nat -> Set} -> CutKit X -> CutKit (Box X)
boxCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) -> wl +N wr == w ->
        Box X (w , h) -> Box X (wl , h) * Box X (wr , h)
  clr w h wl wr wq (tile x) with cutLR w h wl wr wq x
  clr w h wl wr wq (tile x) | xl , xr = tile xl , tile xr
  clr w h wl wr wq (leri wl' bl wr' br wq')
    with cutCompare wl wr wl' wr' w wq wq'
  clr w h wl wr wq (leri wl' bl wr' br wq')
    | cutLt d lq rq with clr wl' h wl (suc d) lq bl
  clr w h wl wr wq (leri wl' bl wr' br wq')
    | cutLt d lq rq | bll , blr = bll , leri (suc d) blr wr' br rq
  clr w h wl wr wq (leri .wl bl .wr br wq')
    | cutEq refl refl = bl , br
  clr w h wl wr wq (leri wl' bl wr' br wq')
    | cutGt d lq rq with clr wr' h (suc d) wr rq br
  clr w h wl wr wq (leri wl' bl wr' br wq')
    | cutGt d lq rq | brl , brr = leri wl' bl (suc d) brl lq , brr
  clr w h wl wr wq (tobo ht bt hb bb x)
    with clr w ht wl wr wq bt | clr w hb wl wr wq bb
  clr w h wl wr wq (tobo ht bt hb bb x)
    | tl , tr | bl , br = tobo ht tl hb bl x , tobo ht tr hb br x
  -- clr w h wl wr wq b = {!!}
  ctb : (w h ht hb : Nat) -> ht +N hb == h ->
        Box X (w , h) -> Box X (w , ht) * Box X (w , hb)
  ctb w h ht hb hq (tile x ) with cutTB w h ht hb hq x
  ctb w h ht hb hq (tile x ) | xt , xb = tile xt , tile xb
  ctb w h ht hb hq (leri wl bl wr br x)
    with ctb wl h ht hb hq bl | ctb wr h ht hb hq br
  ctb w h ht hb hq (leri wl bl wr br x)
    | lt , lb | rt , rb = leri wl lt wr rt x , leri wl lb wr rb x
  ctb w h ht hb hq (tobo ht' bt hb' bb hq')
    with cutCompare ht hb ht' hb' h hq hq'
  ctb w h ht hb hq (tobo ht' bt hb' bb hq')
    | cutLt d tq bq with ctb w ht' ht (suc d) tq bt
  ctb w h ht hb hq (tobo ht' bt hb' bb hq')
    | cutLt d tq bq | btt , btb = btt , tobo (suc d) btb hb' bb bq
  ctb w h ht hb hq (tobo .ht bt .hb bb hq')
    | cutEq refl refl = bt , bb
  ctb w h ht hb hq (tobo ht' bt hb' bb hq')
    | cutGt d tq bq with ctb w hb' (suc d) hb bq bb
  ctb w h ht hb hq (tobo ht' bt hb' bb hq')
    | cutGt d tq bq | bbt , bbb = tobo ht' bt (suc d) bbt tq , bbb
  -- ctb w h ht hb hq b = {!!}


---------------------------------------------------------------------------
-- CROP                                                                  --
---------------------------------------------------------------------------

-- Show that, given a CutKit, you can implement the "crop" operation which
-- trims a small rectangle out of an enclosing rectangle.
-- (1 mark)

crop : {X : Nat * Nat -> Set} -> CutKit X ->
       (wl wc wr ht hc hb : Nat) ->
       X ((wl +N wc +N wr) , (ht +N hc +N hb)) -> X (wc , hc)
crop ck wl wc wr ht hc hb x
  = fst (cutLR _ _ _ wr refl (snd (cutLR _ _ wl _ refl
       (fst (cutTB _ _ _ hb refl (snd (cutTB _ _ ht _ refl x))))
    ))) where
  open CutKit ck
-- crop ck wl wc wr ht hc hb x = {!!}

-- For fun, practice, and the chance to test your work, try building
-- a nontrivially tiled...

testBigBox : Box (HoleOr (Matrix Char)) (20 , 15)
testBigBox = -- {!!}
  leri
   3 (tile hole)
   17 (leri
    10 (tobo
     6 (tile hole)
     9 (tobo
      3 (tile (stuff ( [- "marmalades" -] :: [- "cantilever" -] :: [- "balderdash" -]
          :: [] ) ) )
      6 (tile (stuff (vec (vec '*') ) ) )
   refl) refl)
  7 (tile hole) refl) refl

-- ...so that you can see this stuff in action:

textDisplayCutKit : CutKit (Box (HoleOr (Matrix Char)))
textDisplayCutKit = boxCutKit (holeCutKit matrixCutKit)

testWeeBox : Box (HoleOr (Matrix Char)) (10 , 5)
testWeeBox = crop textDisplayCutKit 5 10 5 5 5 5 testBigBox


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
-- to see through the holes.

mask : {X Y Z : Nat * Nat -> Set} -> CutKit Y ->
       [ X -:> Box Y -:> Box Z ] ->
                     [
       {- front -}     Box X -:>
       {- back  -}     Box Y -:>
       {- combined -}  Box Z ]
mask {X}{Y}{Z} ck m = go where
  open CutKit (boxCutKit ck)
  go : [ Box X -:> Box Y -:> Box Z ]
  go (tile x) yb = m x yb
  go (leri wl xlb wr xrb wq) yb with cutLR _ _ wl wr wq yb
  go (leri wl xlb wr xrb wq) yb | ylb , yrb
    = leri wl (go xlb ylb) wr (go xrb yrb) wq
  go (tobo ht xtb hb xbb hq) yb with cutTB _ _ ht hb hq yb
  go (tobo ht xtb hb xbb hq) yb | ytb , ybb
    = tobo ht (go xtb ytb) hb (go xbb ybb) hq

-- Check that you can indeed see through holes in the front to the
-- tiling at the back.
seeThrough : {X : Nat * Nat -> Set} -> CutKit X ->
                        [
          {- front -}     Box (HoleOr X) -:>
          {- back  -}     Box X -:>
          {- combined -}  Box X ]
seeThrough ck = mask ck \ { hole b -> b ; (stuff x) b -> tile x }

-- Now go further, and make Box (HoleOr X) a monoid for all widths and heights,
-- where the monoid operation is superimposition of holey overlays.
-- That is, there is such a thing as a totally
-- transparent layer, and you can overlay *any* number of layers by
-- combining any two neighbouring layers at a time.

-- I don't require you to prove the monoid laws, apart from left unit, which
-- should be very easy if you've done the thing a sensible way.

postulate IGiveUp : {X : Set} -> X

overlayMonoid : {X : Nat * Nat -> Set} -> CutKit X -> {wh : Nat * Nat} ->
  Monoid (Box (HoleOr X) wh)
overlayMonoid {X} ck {wh} =
  record { e = tile hole
         ; op = overlay
         ; lunit = \ m -> refl
         ; runit = IGiveUp
         ; assoc = IGiveUp
         } where
    over1 : [ HoleOr X -:> Box (HoleOr X) -:> Box (HoleOr X) ]
    over1 hole b = b
    over1 f _ = tile f
    overlay : [ Box (HoleOr X) -:> Box (HoleOr X) -:> Box (HoleOr X) ]
    overlay = mask (holeCutKit ck) over1

accumulate : forall {X Y} -> Monoid Y -> (X -> Y) -> List X -> Y
accumulate {X}{Y} m f = go where
  open Monoid m
  go : List X -> Y
  go [] = e
  go (x :: xs) = op (f x) (go xs)


-- For fun, and the shape of things to come, build two box tilings.
-- Make sure each has a rectangle of text in the middle and Hole all
-- around. Make sure that the rectangles overlap each other, but not
-- completely. See what happens when you overlay them, either way
-- around.

module TestOverlay where

  open module _Goo {X}{wh : Nat * Nat}
    = Monoid (overlayMonoid (matrixCutKit {X}){wh})

  rectangleA : Box (HoleOr (Matrix Char)) (20 , 15)
  rectangleA = -- {!!}
    leri 3 (tile hole) 17 (leri 10
     (tobo 3 (tile hole) 12 (tobo 6
      (tile (stuff (
          [- "+--------+" -] ::
          [- "|Let joy |" -] ::
          [- "|be uncon|" -] ::
          [- "|fined!  |" -] ::
          [- "|(thanks)|" -] ::
          [- "+--------+" -] :: [] )))  6 (tile hole) refl) refl)
    7 (tile hole) refl) refl

  rectangleB : Box (HoleOr (Matrix Char)) (20 , 15)
  rectangleB = -- {!!}
    leri 7 (tile hole) 13 (leri 10
     (tobo 6 (tile hole) 9 (tobo 6 
      (tile (stuff (
          [- "+--------+" -] ::
          [- "|My heart|" -] ::
          [- "|has gone|" -] ::
          [- "|but I   |" -] ::
          [- "|live on.|" -] ::
          [- "+--------+" -] :: [] ))) 3 (tile hole) refl) refl)
    3 (tile hole) refl) refl

  frontA_backB : Matrix Char (20 , 15)
  frontA_backB = renderHoleOrText (op rectangleA rectangleB)

  frontB_backA : Matrix Char (20 , 15)
  frontB_backA = renderHoleOrText (op rectangleB rectangleA)


---------------------------------------------------------------------------
-- CURSES DISPLAY FOR APPLICATIONS (5 marks)                             --
---------------------------------------------------------------------------

-- You may need to look at the Ex6-Setup file to find some of the relevant
-- kit for this episode, and it's worth looking there for goodies, anyway.
-- We start from the idea of a main loop.

{- This is the bit of code I wrote in Haskell to animate your code. -}
postulate
  mainAppLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S ** List Action) ->              -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO One
{-# COMPILED mainAppLoop (\ _ -> HaskellSetup.mainAppLoop) #-}


-- To make a thing you can run, you need to
--   (i)    choose a type to represent the program's internal state S
--   (ii)   give the initial state
--   (iii)  explain how, given an event and the current state, to
--            produce a new state and a list of actions to update the
--            display.


---------------------------------------------------------------------------
-- PAINTINGS                                                             --
---------------------------------------------------------------------------

-- Now that we're in colour, one cell of display will be a ColourChar ...

data ColourChar : Set where
  _-_/_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar

-- ... e.g.     green - '*' / black    for a green * on black.

-- a painting is a Box structure whose basic tiles are either transparent
-- holes or opaque rectangles of coloured text.

Painting : Nat * Nat -> Set
Painting = Box (HoleOr (Matrix ColourChar))

-- Now your turn. Making use of the equipment you developed in epsiode 2,
-- get us from a Painting to a List Action in two hops. Note that you will
-- have to decide how to render a hole: some bland background stuff, please.
-- (1 mark)

paintMatrix : [ Painting -:> Matrix ColourChar ]
paintMatrix p = pasteBox matrixPasteKit (mapIx fill p) where
  open FunctorIx (monadFunctorIx boxMonadIx)
  fill : [ HoleOr (Matrix ColourChar) -:> Matrix ColourChar ]
  fill hole = vec (vec (black - ' ' / white))
  fill (stuff m) = m

vecFoldR : {X Y : Set} -> (X -> Y -> Y) -> Y -> {n : Nat} -> Vec X n -> Y
vecFoldR c n [] = n
vecFoldR c n (x :: xs) = c x (vecFoldR c n xs)

paintAction : {wh : Nat * Nat} -> Matrix ColourChar wh -> List Action
paintAction = vecFoldR (vecFoldR (\ {(f - c / b) k -> \ as ->
  fgText f :: bgText b :: sendText (c :: []) :: k as}) id) []


---------------------------------------------------------------------------
-- APPLICATIONS                                                          --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- You need to choose some sort of size-dependent state, then provide these
-- bits and pieces. We need to know how the state is updated according to
-- events, with resizing potentially affecting the state's type. We must
-- be able to paint the state. The state should propose a cursor position.
-- (Keen students may modify this definition to ensure the cursor must be
-- within the bounds of the application.)

record Application (wh : Nat * Nat) : Set where
  coinductive
  field
    handleKey     : Key -> Application wh
    handleResize  : (wh' : Nat * Nat) -> Application wh'
    paintMe       : Painting wh
    cursorMe      : Nat * Nat  -- x,y coords
open Application public

-- Now your turn. Build the appropriate handler to connect these
-- applications with mainAppLoop. Again, work in two stages, first
-- figuring out how to do the right actions, then managing the
-- state properly. (1 mark)

_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x :: xs) +L ys = x :: (xs +L ys)
infixr 3 _+L_

APP : Set
APP = Sg (Nat * Nat) Application

appPaint : APP -> List Action
appPaint (_ , app) =
  goRowCol 0 0 :: (paintAction o paintMatrix) p
     -- must have composition here, to work around compiler bug
     -- paintAction (paintMatrix p)
     -- segfaults, because p is erased
  +L (goRowCol (snd xy) (fst xy) :: [])
  where
    p  = paintMe app
    xy = cursorMe app

appHandler : Event -> APP -> APP ** List Action
appHandler (key k) (wh , app) = app' , appPaint app'
  where
    app' : APP
    app' = _ , handleKey app k
appHandler (resize w h) (wh , app) = app' , appPaint app'
  where
    app' : APP
    app' = _ , handleResize app (w , h)

appMain : (forall {wh} -> Application wh) -> IO One
appMain app = mainAppLoop ((0 , 0) , app) appHandler
  -- will get resized dynamically to size of terminal, first thing


---------------------------------------------------------------------------
-- DEMO, MADE INTO AN APPLICATION                                       --
---------------------------------------------------------------------------

sillyChar : Char -> forall {wh} -> Painting wh
sillyChar c = tile (stuff (vec (vec (green - c / black)) ))

sillyApp : forall {wh} -> Char -> Application wh
handleKey    (sillyApp _) (char c) = sillyApp c
handleKey    (sillyApp c) _ = sillyApp c
handleResize (sillyApp c) wh' = sillyApp c
paintMe      (sillyApp {suc (suc w) , suc (suc h)} c) =
  tobo 1 (sillyChar c)
          (suc h) (tobo h
            (leri 1 (sillyChar c) (suc w)
             (leri w (sillyChar ' ') 1 (sillyChar c) (plusCommFact w 1))
             refl)
            1 (sillyChar c) (plusCommFact h 1) )
          refl
paintMe      (sillyApp {_} c) = sillyChar c
cursorMe     (sillyApp c) = 0 , 0

{-+}
main : IO One
main = appMain (sillyApp '*')
{+-}


---------------------------------------------------------------------------
-- COMPARING TWO NUMBERS                                                 --
---------------------------------------------------------------------------

-- You've done the tricky part in episode 3, comparing two splittings of
-- the same number. Here's an easy way to reuse that code just to compare
-- two numbers. It may help in what is to come.

Compare : Nat -> Nat -> Set
Compare x y = CutCompare x y y x (x +N y)

compare : (x y : Nat) -> Compare x y
compare x y = cutCompare x y y x (x +N y) refl (plusCommFact y x)

-- To make sure you've got the message, try writing these things
-- "with compare" to resize paintings. If you need to make a painting
-- bigger, pad its right or bottom with a hole. If you need to make it
-- smaller, trim off the right or bottom excess. You have all the gadgets
-- you need! I'm not giving marks for these, but they'll be useful in
-- the next bit.

cropPadLR : (w h w' : Nat) -> Painting (w , h) -> Painting (w' , h)
cropPadLR w h w' p with compare w w'
cropPadLR w h w' p | cutLt d q _ = leri w p (suc d) (tile hole) q
cropPadLR w h .w p | cutEq refl _ = p
cropPadLR w h w' p | cutGt d q _
  = fst (CutKit.cutLR (boxCutKit (holeCutKit matrixCutKit))
         w h w' (suc d) q p)

cropPadTB : (w h h' : Nat) -> Painting (w , h) -> Painting (w , h')
cropPadTB w h h' p with compare h h'
cropPadTB w h h' p | cutLt d q _ = tobo h p (suc d) (tile hole) q
cropPadTB w h .h p | cutEq refl _ = p
cropPadTB w h h' p | cutGt d q _
  = fst (CutKit.cutTB (boxCutKit (holeCutKit matrixCutKit))
         w h h' (suc d) q p)


---------------------------------------------------------------------------
-- THE MOVING RECTANGLE                                                  --
---------------------------------------------------------------------------

-- This is the crux of the episode. Please build me an application which
-- displays a movable resizeable rectangle drawn with ascii art as follows
--
--           +--------------+
--           |              |
--           |              |
--           +--------------+
--
-- The "size" of the application is the terminal size: the rectangle should
-- be freely resizable *within* the terminal, so you should pad out the
-- rectangle to the size of the screen using "hole".
-- That is, only the rectangle is opaque; the rest is transparent.
-- The background colour of the rectangle should be given as an argument.
-- The foreground colour of the rectangle should be white.
-- The rectangle should have an interior consisting of opaque space with
-- the given background colour.
--
-- The arrow keys should move the rectangle around inside the terminal
-- window, preserving its size (like when you drag a window around).
-- Shifted arrow keys should resize the rectangle by moving its bottom
-- right corner (again, like you might do with a mouse).
-- You do not need to ensure that the rectangle fits inside the terminal.
-- The cursor should sit at the bottom right corner of the rectangle.
--
-- Mac users: the Terminal application which ships with OS X does NOT
-- give the correct treatment to shift-up and shift-down. You can get a
-- suitable alternative from http://iterm2.com/ (Thank @sigfpe for the tip!)
--
-- (2 marks, one for key handling, one for painting)

record RectState : Set where
  constructor rect
  field
    gapL rectW : Nat
    gapT rectH : Nat

rectKey : Key -> RectState -> RectState
rectKey (arrow normal up) (rect gapL rectW (suc gapT) rectH)
  = rect gapL rectW gapT rectH
rectKey (arrow normal down) (rect gapL rectW gapT rectH)
  = rect gapL rectW (suc gapT) rectH
rectKey (arrow normal left) (rect (suc gapL) rectW gapT rectH)
  = rect gapL rectW gapT rectH
rectKey (arrow normal right) (rect gapL rectW gapT rectH)
  = rect (suc gapL) rectW gapT rectH
rectKey (arrow shift up) (rect gapL rectW gapT (suc rectH))
  = rect gapL rectW gapT rectH
rectKey (arrow shift down) (rect gapL rectW gapT rectH)
  = rect gapL rectW gapT (suc rectH)
rectKey (arrow shift left) (rect gapL (suc rectW) gapT rectH)
  = rect gapL rectW gapT rectH
rectKey (arrow shift right) (rect gapL rectW gapT rectH)
  = rect gapL (suc rectW) gapT rectH
rectKey _ s = s

rectApp : Colour -> RectState -> forall {wh} -> Application wh
handleKey    (rectApp c r) k   = rectApp c (rectKey k r)
handleResize (rectApp c r) wh' = rectApp c r
paintMe      (rectApp c (rect gapL rectW gapT rectH))
  = cropPadTB _ _ _ (cropPadLR _ _ _
       (tobo gapT (tile hole) (suc (rectH +N 1))
        (leri gapL (tile hole) (suc (rectW +N 1))
         (tobo 1 (horiz rectW) _
         (tobo rectH
           (leri 1 (vert rectH) _ 
           (leri rectW (interior (rectW , rectH)) 
           1 (vert rectH) refl) refl) 
         1 (horiz rectW) refl) refl)
       refl) refl)) where
  horiz : (w : Nat) -> Painting (suc (w +N 1) , 1)
  horiz w = leri 1 (tile (stuff ((white - '+' / c :: []) :: []) )) _
    (leri w (tile (stuff (vec (white - '-' / c) :: [] ))) 1
      (tile (stuff ((white - '+' / c :: []) :: [] ))) refl) refl
  vert : (h : Nat) -> Painting (1 , h)
  vert h = tile (stuff (vec (vec (white - '|' / c)) ))
  interior : (wh : Nat * Nat) -> Painting wh
  interior _ = tile (stuff (vec (vec (white - ' ' / c)) ))
cursorMe     (rectApp c (rect gapL rectW gapT rectH)) =
  (1 +N gapL +N rectW) , (1 +N gapT +N rectH)

{-+}
main : IO One
main = appMain (rectApp blue (rect 10 40 3 15))
{+-}


---------------------------------------------------------------------------
-- LAYERING APPLICATIONS                                                 --
---------------------------------------------------------------------------

rotate : forall {X} -> List X -> List X
rotate [] = []
rotate (x :: xs) = xs +L (x :: [])

safeHead : forall {X} -> X -> List X -> X
safeHead x []        = x
safeHead _ (x :: xs) = x

mapL : forall {X Y} -> (X -> Y) -> List X -> List Y
mapL f [] = []
mapL f (x :: xs) = f x :: mapL f xs

defaultRect : RectState
defaultRect = rect 10 40 3 15

layered : forall {wh} -> List Colour -> List (Application wh) -> Application wh
handleKey (layered cs as)        escape  =
  layered (rotate cs) (rectApp (safeHead red cs) defaultRect :: as)
handleKey (layered cs as)        tab     = layered cs (rotate as)
handleKey (layered cs [])        delete  = layered cs []
handleKey (layered cs (a :: as)) delete  = layered cs as
handleKey (layered cs [])        k       = layered cs []
handleKey (layered cs (a :: as)) k       = layered cs (handleKey a k :: as)
handleResize (layered cs as) wh' =
  layered cs (mapL (\ a -> handleResize a wh') as)
paintMe      (layered cs as) =
  accumulate (overlayMonoid matrixCutKit) paintMe as
cursorMe (layered cs [])       = 0 , 0
cursorMe (layered cs (a :: _)) = cursorMe a

{-(-}
main : IO One
main = appMain (layered
  (blue :: red :: green :: magenta :: cyan :: yellow :: [])
  [])
{-)-}

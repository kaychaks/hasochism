{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}
module Boxes where

-- import Papa ()
import           Lib

-- *** /Separated Conjunction/
--
-- | separating conjunction of two indexed type constructors is an indexed product whose index is also a product, in which each component of the indexed product is indexed by the component of the index
data (p :: t -> *) :**: (q :: k -> *) :: (t,k) -> * where
  (:&&:) :: p t -> q k -> (p :**: q) '(t,k)

type Size = Natty :**: Natty

-- *** Box
--
-- | A box @b@ with content of size-indexed type @p@ and size @wh@ has type @'Box' p wh@
-- Boxes are constructed from content('Stuff'), clear boxes ('Clear'), and horizontal ('Hor') and vertical ('Ver') composition
data Box :: ((Nat, Nat) -> *) -> (Nat, Nat) -> * where
  Stuff :: p wh -> Box p wh
  Clear :: Box p wh
  Hor :: Natty w1 -> Box p '(w1,h) ->
        Natty w2 -> Box p '(w2,h) -> Box p '(w1 :+ w2, h)
  Ver :: Natty h1 -> Box p '(w,h1) ->
        Natty h2 -> Box p '(w,h2) -> Box p '(w, h1 :+ h2)


-- *** Juxtaposition
--
-- $doc
-- a natural operation that juxtaposes two boxes together, horizontally or vertically, adding appropriate padding if the sizes don't match up

-- | horizontal version
--
juxH :: Size '(w1,h1) -> Size '(w2,h2) -> Box p '(w1,h1) -> Box p '(w2,h2) -> Box p '(w1 :+ w2, Max h1 h2)
juxH (w1 :&&: h1) (w2 :&&: h2) b1 b2 = case cmp h1 h2 of
  LTNat z -> Hor w1 (Ver h1 b1 (Sy z) Clear) w2 b2
  EQNat   -> Hor w1 b1 w2 b2
  GTNat z -> Hor w1 b1 w2 (Ver h2 b2 (Sy z) Clear)

-- | vertical version
--
juxV :: Size '(w1,h1) -> Size '(w2,h2) -> Box p '(w1,h1) -> Box p '(w2,h2) -> Box p '(Max w1 w2, h1 :+ h2)
juxV (w1 :&&: h1) (w2 :&&: h2) b1 b2 = case cmp w1 w2 of
  LTNat z -> Ver h1 (Hor w1 b1 (Sy z) Clear) h2 b2
  EQNat   -> Ver h1 b1 h2 b2
  GTNat z -> Ver h1 b1 h2 (Hor w2 b2 (Sy z) Clear)


-- *** Cutting

-- | Special kind of comparision required to handle the case in which we horizontally cut the horizontal composition of two boxes
--
-- given the equation @a + b = c + d@,
--
-- if @a < c@ then there must exist some number @z@, such that
--
-- @b = (z + 1) + d@ and @c = a + (z + 1)@
data CmpCuts :: Nat -> Nat -> Nat -> Nat -> * where
  LTCuts :: (b ~ (S z :+ d), c ~ (a :+ S z)) => Natty z -> CmpCuts a b c d
  EQCuts :: (a ~ c, b ~ d) => CmpCuts a b c d
  GTCuts :: (d ~ (S z :+ b), a ~ (c :+ S z)) => Natty z -> CmpCuts a b c d

cmpCuts :: ((a :+ b) ~ (c :+ d)) => Natty a -> Natty b -> Natty c -> Natty d -> CmpCuts a b c d
cmpCuts Zy b Zy d = EQCuts
cmpCuts Zy b (Sy c) d = LTCuts c
cmpCuts (Sy a) b Zy d = GTCuts a
cmpCuts (Sy a) b (Sy c) d = case cmpCuts a b c d of
  LTCuts z -> LTCuts z
  EQCuts   -> EQCuts
  GTCuts z -> GTCuts z

-- | for cutting up boxes, and two-dimensional entities in general
--
class Cut (p :: (Nat, Nat) -> *) where
  horCut :: Natty m -> Natty n -> p '(m :+ n, h) -> (p '(m,  h) , p '(n, h))
  verCut :: Natty m -> Natty n -> p '(w, m :+ n) -> (p '(w, m) , p '(w, n))

instance Cut p => Cut (Box p) where
  horCut m n (Stuff p) = (Stuff p1, Stuff p2) where
    (p1, p2) = horCut m n p
  horCut m n Clear = (Clear, Clear)
  horCut m n (Hor w1 b1 w2 b2) = case cmpCuts m n w1 w2 of
    LTCuts z -> let (b11, b12) = horCut m (Sy z) b1
                   in (b11, Hor (Sy z) b12 w2 b2)
    EQCuts -> (b1, b2)
    GTCuts z -> let (b21,b22) = horCut (Sy z) n b2
                   in (Hor w1 b1 (Sy z) b21, b22)
  horCut m n (Ver h1 b1 h2 b2) = let (b11, b12) = horCut m n b1
                                     (b21, b22) = horCut m n b2
                                     in
                                   (Ver h1 b11 h2 b21, Ver h1 b12 h2 b22)

  verCut m n (Stuff p) = let (p1, p2) = verCut m n p
                             in
                           (Stuff p1, Stuff p2)
  verCut m n Clear = (Clear, Clear)
  verCut m n (Hor w1 b1 w2 b2) = let (b11, b12) = verCut m n b1
                                     (b21, b22) = verCut m n b2
                                     in
                                   (Hor w1 b11 w2 b21, Hor w1 b12 w2 b22)

  verCut m n (Ver h1 b1 h2 b2) = case cmpCuts m n h1 h2 of
    LTCuts z -> let (b11, b12) = verCut m (Sy z) b1
                   in
                 (b11, Ver (Sy z) b12 h2 b2)
    EQCuts -> (b1, b2)
    GTCuts z -> let (b21, b22) = verCut (Sy z) n b2
                   in
                 (Ver h1 b1 (Sy z) b21, b22)

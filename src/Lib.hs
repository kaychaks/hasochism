{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Lib
where

-- import           GHC.TypeNats hiding (Nat (..))
import           Papa    hiding ((:<), (:>), Max)
import           Prelude ()

data Nat = Z | S Nat deriving (Show, Eq, Ord)

-- | Vector GADT
data Vec :: Nat -> * -> * where
  V0 :: Vec 'Z x
  (:>) :: x -> Vec n x -> Vec ('S n) x

vcopies :: forall n x. Natty n -> x -> Vec n x
vcopies Zy _      = V0
vcopies (Sy n') x = x :> vcopies n' x

vapp :: forall n s t. Vec n (s -> t) -> Vec n s -> Vec n t
vapp V0 V0               = V0
vapp (f :> fs) (s :> ss) = f s :> vapp fs ss

instance NATTY n => Applicative (Vec n) where
  pure = vcopies natty
  (<*>) = vapp

instance Foldable (Vec n) where
  foldMap = foldMapDefault

instance Traversable (Vec n) where
  traverse _ V0        = pure V0
  traverse f (x :> xs) = (:>) <$> f x <*> traverse f xs

instance Functor (Vec n) where
  fmap = fmapDefault

-- | Singleton GADT for the run time replica of the static data type 'Nat'
--
-- Each type level value /n/ in 'Nat' kind is represented uniquely in the type 'Natty n'
--
data Natty :: Nat -> * where
  Zy :: Natty 'Z
  Sy :: Natty n -> Natty ('S n)

-- | Singleton class for implicit /PI/ types
--
class NATTY (n :: Nat) where
  natty :: Natty n
instance NATTY 'Z where
  natty = Zy
instance NATTY n' => NATTY ('S n') where
  natty = Sy natty

-- *** Merge Sort

-- | defining /<=/ as a \'type\' class, seen as a relation
--
-- m <= n
class LeN (m :: Nat) (n :: Nat) where
-- | 0 <= n
instance LeN Z n where
-- | m <= n -> (m + 1) <= (n + 1)
instance LeN m n => LeN (S m) (S n) where

-- | capturing the essence of numbers can be sorted /one way or the other/ (OWOTO)
data OWOTO :: Nat -> Nat -> * where
  LE :: LeN x y => OWOTO x y
  GE :: LeN y x => OWOTO x y

-- | putting numbers in order
owoto :: forall m n. Natty m -> Natty n -> OWOTO m n
owoto Zy _ = LE
owoto (Sy _) Zy = GE
owoto (Sy m) (Sy n) = case owoto m n of
  LE -> LE
  GE -> GE

-- **** creating ordered lists

-- | concept of bounds to talk about the kind of elements in an ordered list
-- there will be a bottom element which is <= than the first element and then there will
-- be a top element which is >= than the last element of the list. and there will be all
-- those other elements in between bottom and top
data Bound x = Bot | Val x | Top deriving (Show, Eq, Ord)

-- | to augment instance inferencing, extending the notion of <= on bounds
class LeB (a :: Bound Nat) (b :: Bound Nat) where
instance LeB 'Bot b where
instance LeB ('Val x) ('Val y) where
instance LeB ('Val x) 'Top where
instance LeB 'Top 'Top where

-- | An ordered list is a sequence such that
-- @ l <= x1 <= x2 <= x3 <= ... <= xn <= u @
-- where @l@ and @u@ are the bottom and top respectively
data OList :: Bound Nat -> Bound Nat -> * where
  ONil :: LeB l u => OList l u
  (:<) :: forall l x u. LeB l ('Val x) =>
    Natty x -> OList ('Val x) u -> OList l u

-- | merge operation for ordered lists
merge :: OList l u -> OList l u -> OList l u
merge ONil lu = lu
merge lu ONil = lu
merge (x :< xu) (y :< yu) = case owoto x y of
  LE -> x :< merge xu (y :< yu)
  GE -> y :< merge (x :< xu) yu

-- **** some boilerplate to promote ordinary list of Nats to being considered for ordered lists

-- | genereal data type for existential quantification
data Ex (p :: k -> *) where
  Ex :: p i -> Ex p

type WNat = Ex Natty

wrapNat :: Nat -> WNat
wrapNat Z     = Ex Zy
wrapNat (S m) = case wrapNat m of Ex n -> Ex (Sy n)

-- **** sorting algo
--
divide :: [x] -> ([x],[x])
divide [] = ([],[])
divide (x : xs) = (x : zs, ys) where (ys,zs) = divide xs

msort :: [Nat] -> OList Bot Top
msort [] = ONil
msort [n] = case wrapNat n of Ex n -> n :< ONil
msort xs = merge (msort ys) (msort zs) where (ys,zs) = divide xs

-----------------------------------------------------------------------------------------------------------

-- *** Vector Operations

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance S m :+ n = S (m :+ n)

-- | the only point of 'proxy' is to point out that it has the same type at its binding and its usage sites
data Proxy :: k -> * where
  Proxy :: Proxy i

proxy :: f i -> Proxy i
proxy _ = Proxy

vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
vappend V0 ys        = ys
vappend (x :> xs) ys = x :> vappend xs ys

vchop :: Natty m -> Vec (m :+ n) x -> (Vec m x, Vec n x)
vchop Zy xs = (V0, xs)
vchop (Sy m) (x :> xs) = (x :> ys, zs) where
  (ys,zs) = vchop m xs

vtake :: Natty m -> Proxy n -> Vec (m :+ n) x -> Vec m x
vtake Zy n xs            = V0
vtake (Sy m) n (x :> xs) = x :> vtake m n xs

procrustes :: a -> Natty m -> Natty n -> Vec m a -> Vec n a
procrustes p m n xs = case cmp m n of
  LTNat z -> vappend xs (vcopies (Sy z) p)
  EQNat   -> xs
  GTNat z -> vtake n (proxy (Sy z)) xs

-- **** Better comparators

type family Max (m :: Nat) (n :: Nat) :: Nat where
  Max Z n = n
  Max (S m) Z = S m
  Max (S m) (S n) = S (Max m n)

-- | Along with a GADT we will encode lemmas as suitable type equalities in the form of functions of type
--
-- @
-- forall x1...xn. Natty x1 -> ... -> Natty xn -> ((l ~ r) => t) -> t
-- @
--
-- where @l@ and @r@ are the left- and right-hand-side of the equation, and @x1@,..@xn@ are natural number variables that may appear free in the equation. The first @n@ arguments are singleton natural numbers. The last argument represents a context that expects the equation to hold.
--
-- Along with the equations that define the proof object, we can incorporate other equations that encapsulate further knowledge implied by the result of the comparision like equations for computing the maximum of @m@ and @n@ in each case
data Cmp :: Nat -> Nat -> * where
  LTNat :: ((m :+ S z) ~ n, Max m n ~ n) => Natty z -> Cmp m (m :+ S z) -- ^ singleton rep. of @z@ here is the witness of the proof that @m < m + z + 1@
  EQNat :: (m ~ n, Max m n ~ m) => Cmp m m
  GTNat :: (m ~ (n :+ S z), Max m n ~ m) => Natty z -> Cmp (n :+ S z) n -- ^ singleton rep. of @z@ here is the witness of the proof that @n + z + 1 > n@

cmp :: Natty m -> Natty n -> Cmp m n
cmp Zy Zy = EQNat
cmp Zy (Sy n) = LTNat n
cmp (Sy m) Zy = GTNat m
cmp (Sy m) (Sy n) = case cmp m n of
  LTNat z -> LTNat z
  EQNat   -> EQNat
  GTNat z -> GTNat z


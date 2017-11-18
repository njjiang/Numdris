-- ------------------------------------------------------------- [ Field.idr ]
-- Module      : NumIdris.Field
-- Description : Definitions for the interface Field
--
--------------------------------------------------------------------- [ EOH ]
module NumIdris.Field

%access public export

interface (Ord a, Eq a, Num a, Neg a) => Field a where
  zero : a
  one : a
  inv : a -> a

Field Integer where
  zero = 0
  one = 1
  inv = negate

Field Double where
  zero = 0
  one = 1
  inv = negate


zeroIsZero : (Field a) => (x : a) -> zero = zero * x

oneIsIdentity : (Field a) => (x : a) -> x = x * one

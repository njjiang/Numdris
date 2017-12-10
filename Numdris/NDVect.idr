-- ------------------------------------------------------------- [ Tensor.idr ]
-- Module      : Numdris.NDVect
-- Description : n-dimensional vector definitions and operations
--------------------------------------------------------------------- [ EOH ]

module Numdris.NDVect

import Data.Vect
import Data.Complex
import Numdris.Vect.Util
import Numdris.Matrix
import Numdris.Matrix.Algebra as MA
import Numdris.Field

%access public export

infixr 7 <><>

||| n-dimensional vector of with rank and shape encoded in types
NDVect : (rank : Nat) -> (shape : Vect rank Nat) -> Type -> Type
NDVect Z     []      t = t
NDVect (S n) (x::xs) t = Vect x (NDVect n xs t)


||| map an operation on every entry of a tensor
mapT : (f : t -> t) -> (v : NDVect r s t) -> NDVect r s t
mapT {r = Z}   {s = []}    f v = f v
mapT {r = S Z} {s = [x]}   f v = map f v
mapT {r = S (S Z)} {s = [x,y]}   f v = iterateM f v
mapT {r = S _} {s = x::xs} f v = (map {f = Vect x}) (mapT f) v

||| multiply a tensor by a scalar
||| @ c scalar
||| @ v tensor
||| note: there seems to be a compiler bug that such that calling mapT does not type check
scale : (Num t) => (c : t) -> (v : NDVect rank shape t) -> NDVect rank shape t
scale c v = mapT (*c) v


||| computes the tensor product ⊗
(<><>) : Num t => (v: NDVect r shape t) ->
                  (w: NDVect r' shape' t) ->
                  NDVect (r + r') (shape ++ shape') t
(<><>) {r = Z}   {shape = []}    v w = scale v w
(<><>) {r = S _}  {shape = x::xs} v w = map (\x => x <><> w) v

||| determinant of a n x n matrix/2d vector
determinant : (Field t, Num t) => NDVect 2 [n,n] t -> t
determinant v = Algebra.determinant v

||| get an entry from an NDVect, given a list of indices
entry : NDVect rank shape t -> Vect rank Nat -> Maybe t
entry {rank = Z}     {shape = []} ndv indices = Just ndv
entry {rank = (S n)} {shape = (x::xs)} ndv (i::is) with (natToFin i x)
      | Just fi = entry (Vect.index fi ndv) is
      | Nothing = Nothing

||| expand a NDVect by one dimension
expand : (times : Nat) -> NDVect rank shape t -> NDVect (S rank) (times :: shape) t
expand times v = replicate times v

||| flatten an NDVect to a 1D vector
||| unimplemented for rank > 2
flattenND : NDVect (S rank) shape t -> Vect (Foldable.product shape) t
flattenND {rank = Z} {shape = [x]} v = rewrite multOneRightNeutral x in v
flattenND {rank = S Z} {shape = [x,y]} v = rewrite multOneRightNeutral y in Vect.concat v
-- flattenND {rank = S (S n)} {shape = x::y::xs} {t} v = Vect.concat $ map(flattenND {rank=(S n)} {shape = y::xs} {t=t}) v


||| map a complex field operation
||| as a work around for yet another compiler bug
mapComplex : Num a => (f : (Complex a) -> a) -> (v : NDVect r s (Complex a)) -> NDVect r s a
mapComplex {r = Z}   {s = []}    f v = f v
mapComplex {r = S Z} {s = [x]}   f v = map f v
mapComplex {r = S n} {s = x::xs} f v = map (mapComplex f) v

real : (Num a) => (m : NDVect r shape (Complex a)) -> NDVect r shape a
real {a} m = mapComplex realPart m

imaginary : Num t => (m : NDVect r shape (Complex t)) -> NDVect r shape t
imaginary m = mapComplex imagPart m

conjugate : Neg t => (m : NDVect r shape (Complex t)) -> NDVect r shape (Complex t)
conjugate {t} m = (mapT {t = Complex t}) Complex.conjugate m

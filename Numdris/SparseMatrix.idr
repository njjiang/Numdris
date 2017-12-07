-- ------------------------------------------------------------- [ Matrix.idr ]
-- Module      : Numdris.SparseMatrix
-- Description : Definitions for sparse matrices
--
--------------------------------------------------------------------- [ EOH ]

module Numdris.SparseMatrix

import Data.Vect
import Data.SortedMap
import Data.Complex
import Numdris.Field
import Numdris.Matrix
import Numdris.Matrix.Algebra
import Numdris.Vector

%access public export

||| a sparse matrix of size r x c has a mapping from indices to nonzero values
data SparseMatrix : (r : Nat) -> (c : Nat) -> (t : Type) -> Type where
     MkSparseMatrix : (indexValueMap : SortedMap (Fin r, Fin c) t) -> SparseMatrix r c t


indexValueMap : SparseMatrix r c t -> SortedMap (Fin r, Fin c) t
indexValueMap (MkSparseMatrix indvals) = indvals

nonzeroIndices : SparseMatrix r c t -> List (Fin r, Fin c)
nonzeroIndices m = (map Basics.fst) . toList $ (indexValueMap m)

nonzeroValues : SparseMatrix r c t -> List t
nonzeroValues m = (map Basics.snd) . toList $ (indexValueMap m)

replaceAll : List ((Fin r, Fin c), t) -> List (Matrix r c t -> Matrix r c t)
replaceAll {r} {c} indvals = map (uncurry replaceEntry) indvals

||| successively apply a list of function to a value
successiveApply : List (a -> a) -> a -> a
successiveApply [] a = id a
successiveApply (f::fs) a = successiveApply fs (f a)

||| computes the correspoding matrix for a sparse matrix
toMatrix : Num t => SparseMatrix r c t -> Matrix r c t
toMatrix {r} {c} (MkSparseMatrix Empty) = zerosM r c
toMatrix {r} {c} (MkSparseMatrix indvals) = successiveApply (replaceAll (toList indvals)) (zerosM r c)

||| computes the sparse matrix given a matrix
fromMatrix : (Field t) => Matrix r c t -> SparseMatrix r c t
fromMatrix [[]] = MkSparseMatrix empty
fromMatrix {r} {c} m = MkSparseMatrix (fromList indvals) where
               indvals : List ((Fin r, Fin c), t)
               indvals = (nonzeros {r=r} {c=c}) m


||| replace an entry in a sparse matrix
replaceEntry : (Field t) => (pos : (Fin r, Fin c)) -> (elem : t) -> SparseMatrix r c t -> SparseMatrix r c t
replaceEntry pos zero (MkSparseMatrix indvals) = MkSparseMatrix $ delete pos indvals
replaceEntry pos elem (MkSparseMatrix indvals) = MkSparseMatrix $ insert pos elem indvals

||| look up an entry from a sparse matrix
entry : (Field t) => (Fin r, Fin c) -> SparseMatrix r c t -> t
entry pos (MkSparseMatrix indvals) with (lookup pos indvals)
      | Just v = v
      | Nothing = zero


getRow : (Num t) => Fin r -> SparseMatrix r c t -> Vect c t
getRow {r} {c} {t} row m = successiveApply replaceAllV (zeros c) where
                           indvals : SortedMap (Fin r, Fin c) t
                           indvals = indexValueMap m
                           rowindvals : List ((Fin r, Fin c), t)
                           rowindvals = filter (\((i,j),v) => i == row) (toList indvals)
                           replaceAllV : List (Vect c t -> Vect c t)
                           replaceAllV = map (\((i,j),v) => replaceAt j v) rowindvals

getColumn : (Num t) => Fin c -> SparseMatrix r c t -> Vect r t
getColumn {r} {c} {t} col m = successiveApply replaceAllV (zeros r) where
                              indvals : SortedMap (Fin r, Fin c) t
                              indvals = indexValueMap m
                              colindvals : List ((Fin r, Fin c), t)
                              colindvals = filter (\((i,j),v) => j == col) (toList indvals)
                              replaceAllV : List (Vect r t -> Vect r t)
                              replaceAllV = map (\((i,j),v) => replaceAt i v) colindvals


implementation (Field t, Num t) => Eq (SparseMatrix r c t) where
    (==) = \m1 => \m2 => (==) (toMatrix m1) (toMatrix m2)


add : SparseMatrix r c t -> SparseMatrix r c t -> SparseMatrix r c t

scale : (c : t) -> SparseMatrix r c t -> SparseMatrix r c t

multiply : SparseMatrix r c t -> SparseMatrix r c t -> SparseMatrix r c t

transpose : SparseMatrix r c t -> SparseMatrix c r t

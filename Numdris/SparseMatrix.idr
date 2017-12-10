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
nonzeroIndices m = keys (indexValueMap m)

nonzeroValues : SparseMatrix r c t -> List t
nonzeroValues m = values (indexValueMap m)

replaceAll : List ((Fin r, Fin c), t) -> List (Matrix r c t -> Matrix r c t)
replaceAll {r} {c} indvals = map (uncurry replaceEntry) indvals

||| computes the correspoding matrix for a sparse matrix
toMatrix : Num t => SparseMatrix r c t -> Matrix r c t
-- toMatrix {r} {c} (MkSparseMatrix ) = zerosM r c
toMatrix {r} {c} (MkSparseMatrix indvals) = successiveApply (replaceAll (toList indvals)) (zerosM r c)

||| computes the sparse matrix given a matrix
fromMatrix : (Field t) => Matrix r c t -> SparseMatrix r c t
fromMatrix [[]] = MkSparseMatrix empty
fromMatrix {r} {c} m = MkSparseMatrix (fromList indvals) where
               indvals : List ((Fin r, Fin c), t)
               indvals = (nonzeros {r=r} {c=c}) m


||| replace an entry in a sparse matrix
replaceEntry : (Field t) => (pos : (Fin r, Fin c)) -> (elem : t) -> SparseMatrix r c t -> SparseMatrix r c t
replaceEntry pos elem (MkSparseMatrix indvals) = if elem == zero
                                                 then MkSparseMatrix $ delete pos indvals
                                                 else MkSparseMatrix $ insert pos elem indvals

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

export
scale : (Num t) => t -> SparseMatrix r c t -> SparseMatrix r c t
scale const m = MkSparseMatrix $ fromList $ map (\(ind,val) => (ind, val*const)) (toList (indexValueMap m))



addImpl : (Field t) => SortedMap (Fin r, Fin c) t -> SortedMap (Fin r, Fin c) t -> SortedMap (Fin r, Fin c) t
addImpl {r} {c} m1 m2 = successiveApply updates m2 where
                        keysm1 : List (Fin r, Fin c)
                        keysm1 = keys {k = (Fin r, Fin c)} m1
                        updatem2 : (Fin r, Fin c) -> SortedMap (Fin r, Fin c) t -> SortedMap (Fin r, Fin c) t
                                -> (SortedMap (Fin r, Fin c) t -> SortedMap (Fin r, Fin c) t)
                        updatem2 k m1 m2 = case (lookup k m1, lookup k m2) of
                                          (Just val, Nothing) => insert k val
                                          (Just val1, Just val2) => update k (+val1)
                        updates : List (SortedMap (Fin r, Fin c) t -> SortedMap (Fin r, Fin c) t )
                        updates = map (\k1 => updatem2 k1 m1 m2) keysm1


export
add : (Field t) => SparseMatrix r c t -> SparseMatrix r c t -> SparseMatrix r c t
add {r} {c} {t} (MkSparseMatrix m1) (MkSparseMatrix m2) = MkSparseMatrix ((addImpl{r=r}{c=c}{t=t}) m1 m2)

-- multiply : SparseMatrix r c t -> SparseMatrix r c t -> SparseMatrix r c t
-- multiply {r} {c} {t} (MkSparseMatrix m1) (MkSparseMatrix m2) =

transpose : SparseMatrix r c t -> SparseMatrix c r t
transpose m = MkSparseMatrix $ fromList $ map (\(ind,val) => (swap ind, val)) (toList (indexValueMap m))

emptysparse : SparseMatrix 3 3 Integer
emptysparse = MkSparseMatrix $ fromList []
-- [[0, 2,0],[3,0,0],[0,0,0]]
testsparse : SparseMatrix 3 3 Integer
testsparse = MkSparseMatrix $ fromList [((FS FZ, FZ), 3), ((FZ, FS FZ), 2)]

-- [[1, 42,0],[0,0,0],[0,0,0]]
testsparse1 : SparseMatrix 3 3 Integer
testsparse1 = MkSparseMatrix $ fromList [((FZ, FZ), 1), ((FZ, FS FZ), 42)]

testsparseadd : SparseMatrix 3 3 Integer
testsparseadd = MkSparseMatrix $ fromList [((FZ, FZ), 1), ((FS FZ, FZ), 3), ((FZ, FS FZ), 44)]

-- (add testsparse testsparse1) == testsparseadd
-- True : Bool
-- λΠ> (add testsparse1 testsparse) == testsparseadd
-- True : Bool
-- λΠ> (add emptysparse testsparse) == testsparse
-- True : Bool
-- λΠ> (add testsparse emptysparse) == testsparse
-- True


-- λΠ> toMatrix testsparse
-- [[0, 0, 0], [0, 0, 0], [0, 0, 0]] : Vect 3 (Vect 3 Integer)
-- Type checking ./Numdris/SparseMatrix.idr
-- λΠ> toMatrix testsparse
-- [[0, 2, 0], [3, 0, 0], [0, 0, 0]] : Vect 3 (Vect 3 Integer)
-- λΠ> replaceEntry (FZ, FS FZ) 0 testsparse
-- MkSparseMatrix (M 0 (Leaf (FS FZ, FZ) 3)) : SparseMatrix 3 3 Integer
-- λΠ> toMatrix $ replaceEntry (FZ, FS FZ) 0 testsparse
-- [[0, 0, 0], [3, 0, 0], [0, 0, 0]] : Vect 3 (Vect 3 Integer)

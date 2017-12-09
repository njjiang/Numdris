-- ---------------------------------------------- [ GaussianElimination.idr ]
-- Module      : Numdris.Matrix.GaussianElimination
-- Description : Gaussian elimination
--------------------------------------------------------------------- [ EOH ]

module Numdris.Matrix.GaussianElimination

import Data.Vect
import Data.SortedMap
import Data.Complex
import Numdris.Field
import Numdris.Matrix
import Numdris.Matrix.Algebra
import Numdris.Vector
import Debug.Error

%language ElabReflection
%access public export

data RowOp : Nat -> Type where
     Multiply : Fin r -> Double -> RowOp r
     Add : Fin r -> Double -> Fin r -> RowOp r
     Swap : Fin r -> Fin r -> RowOp r
     Id : RowOp r

||| add updates the first parameter
operate : RowOp r -> Matrix r c Double -> Matrix r c Double
operate (Multiply row s) m = Vect.updateAt row (Vector.scale s) m
operate (Add x scalar y) m = if scalar == 1.0 then Vect.updateAt x (add (getRow y m)) m
                             else Vect.updateAt x (add $ scale scalar (getRow y m)) m
operate (Swap x y) m = swapRows x y m
operate Id m = m

normalizeSelf : Fin r -> Vect c Double -> RowOp r
normalizeSelf _    Nil = Id
normalizeSelf row (x::xs) = if x == 1.0 then Id else Multiply row (1/x)


||| elimiante the first entry of rowx by adding some scalar of row1
eliminateFirstEntry : (row1:Fin r) -> (rowx:Fin r) -> (headRow1:Double) -> (headRowx:Double) -> RowOp r
eliminateFirstEntry row1 rowx r1 x = if x == 0.0
                                     then Id
                                     else Add rowx (negate x/r1) row1


swapForNonzeroFirstPivot : Matrix (S r) (S c) Double -> (Matrix (S r) (S c) Double, RowOp (S r))
swapForNonzeroFirstPivot m {r} = let --indexedFirstColumn : List (Fin (S r), Double)
                                     indexedFirstColumn = toList $ indexed (getColumn {r=S r} FZ m)
                                     -- nonzeros : List (Fin (S r), Double)
                                     nonzeros = filter (\(i,x) => x /= 0.0) indexedFirstColumn
                                 in
                                 case nonzeros of
                                 Nil => error "first column all 0s"
                                 (x::xs) => (swapRows FZ (fst x) m, Swap FZ (fst x))


eliminateColumn : Matrix (S r) (S c) Double -> List (RowOp (S r))
eliminateColumn {r}{c} m@((r1::r1s) :: xx) = if r1 == 0.0
                                             then let (m', swapOp) = swapForNonzeroFirstPivot m
                                             in swapOp :: eliminateColumn m'
                                             else toList $ map (\(i,rx) => eliminateFirstEntry FZ i r1 rx) indexedrows
                                             where
                                             indexedrows : Vect r (Fin (S r), Double)
                                             indexedrows = zip (tail (fins (S r))) (map head xx)



testm : Matrix 3 4 Double
testm = splitVect 3 4 (cast {to=Vect (3*4) Double} (natRangeVect 12))

eliminatetestm : List (RowOp 3)
eliminatetestm = eliminateColumn testm

testm' : Matrix 3 4 Double
testm' = successiveApply ops testm where
         ops : List (Matrix 3 4 Double -> Matrix 3 4 Double)
         ops = map operate eliminatetestm

-- ---------------------------------------------- [ GaussianElimination.idr ]
-- Module      : Numdris.Matrix.GaussianElimination
-- Description : Gaussian elimination
--------------------------------------------------------------------- [ EOH ]

module Numdris.Matrix.GaussianElimination

import Data.Vect
import Data.Complex
import Numdris.Field
import Numdris.Matrix
import Numdris.Matrix.Algebra
import Numdris.Vect.Util
import Debug.Error

%language ElabReflection
%access public export

%default total

data RowOp : Nat -> Type where
     Multiply : Fin r -> Double -> RowOp r
     Add : Fin r -> Double -> Fin r -> RowOp r
     Swap : Fin r -> Fin r -> RowOp r
     Id : RowOp r

Eq (RowOp r) where
  (==) (Multiply x z) (Multiply y w) = (x==y) && (z==w)
  (==) (Add x z w) (Add y s t) = (x==y) && (z==s) && (w==t)
  (==) (Swap x z) (Swap y w) = (x==y) && (z==w)
  (==) Id Id = True
  (==) _ _ = False

||| add updates the first parameter
operate : RowOp r -> Matrix r c Double -> Matrix r c Double
operate (Multiply row s) m = Vect.updateAt row (scale s) m
operate (Add x scalar y) m = if scalar == 1.0 then Vect.updateAt x (add (getRow y m)) m
                             else Vect.updateAt x (add $ scale scalar (getRow y m)) m
operate (Swap x y) m = swapRows x y m
operate Id m = m

normalizeSelf : Fin r -> Vect c Double -> RowOp r
normalizeSelf _    Nil = Id
normalizeSelf row (x::xs) = if x == 1.0 then Id else Multiply row (1/x)


||| elimiante the first entry of rowx by adding some scalar of row1
||| @ pivotRow the index of the row containing pivot
||| @ rowx the index of the row to elmiminate
||| @ pivot the value of the pivot
||| @ entryx the entry below the pivot on rowx
eliminateEntry : (pivotRow:Fin r) -> (rowx:Fin r) -> (pivot:Double) -> (entryx:Double) -> RowOp r
eliminateEntry pivotRow rowx pivot x = if x == 0.0
                                       then Id
                                       else Add rowx (negate x/pivot) pivotRow



subcolumnsAfterIndex : (n : Fin r) -> List t -> List t
subcolumnsAfterIndex n v = drop (S (finToNat n)) v

rowContainsPivot : Vect len Double -> Bool
rowContainsPivot Nil = False
rowContainsPivot (x::xs) = if x /= 0.0 then True else rowContainsPivot xs

swapForNonzeroPivot : Matrix r c Double -> (pivotRow : Fin r) -> (targetCol : Fin c) -> (Matrix r c Double, RowOp r)
swapForNonzeroPivot {r} {c} m pivotRow targetCol = case nonzeroCol of
                                                   Nil => (m, Id)
                                                   (x::xs) => (swapRows pivotRow (fst x) m, Swap pivotRow (fst x))
                                          where
                                          pivotentry : Double
                                          pivotentry = entry (pivotRow, targetCol) m
                                          col : List (Fin r, Double)
                                          col = subcolumnsAfterIndex pivotRow $ toList (zip (fins r) (getColumn targetCol m))
                                          nonzeroCol : List (Fin r, Double)
                                          nonzeroCol = filter (\(i,x) => x /= 0.0) (col)


||| turn the entries on targetCol below pivotRow all 0s
||| by adding some scalar of pivotRow
partial
eliminateColumn : Matrix r c Double -> (targetCol : Fin c) -> (pivotRow : Fin r) -> List (RowOp r)
eliminateColumn {r}{c} m targetCol pivotRow = if pivotentry == 0.0
                                              then let (m', swapOp) = swapForNonzeroPivot m pivotRow targetCol
                                                   in case swapOp of
                                                      Id => []
                                                      Swap _ _ => (swapOp :: eliminateColumn m' targetCol pivotRow)
                                                      _ => error "not gonna happen"
                                              else map (\(i,rx) => eliminateEntry pivotRow i pivotentry rx) col
                                           where
                                           pivotentry : Double
                                           pivotentry = entry (pivotRow, targetCol) m
                                           col : List (Fin r, Double)
                                           col = subcolumnsAfterIndex pivotRow $ toList (zip (fins r) (getColumn targetCol m))





applyOps : List (RowOp r) -> Matrix r c Double -> Matrix r c Double
applyOps ops m = successiveApply (map operate ops) m

partial
eliminateAllColumns' : Matrix r c Double -> List (Fin c, Fin r) -> List (List (RowOp r)) -> (Matrix r c Double, List (List (RowOp r)))
eliminateAllColumns' {r} {c} m [] prev = (m,prev)
eliminateAllColumns' {r} {c} m ((col,row)::xx) prev = let newOps = eliminateColumn m col row
                                                          m' = applyOps newOps m
                                                      in eliminateAllColumns' m' xx (prev ++ [newOps])

partial
eliminateAllColumns : Matrix r c Double -> (Matrix r c Double, List (List (RowOp r)))
eliminateAllColumns {r} {c} m = eliminateAllColumns' m rc []
                              where
                              colIndex : Vect c (Fin c)
                              colIndex = fins c
                              rowIndex : Vect r (Fin r)
                              rowIndex = fins r
                              rc : List (Fin c, Fin r)
                              rc = zip (toList colIndex) (toList rowIndex)



||| find the upper trianglar matrix of some square matrix
partial
findUpper : Matrix n n Double -> (Matrix n n Double, List (List (RowOp n)))
findUpper = eliminateAllColumns

||| invert an operation
invertOp : RowOp r -> RowOp r
invertOp (Multiply x y) = Multiply x (1/y)
invertOp (Add x y z) = Add x (negate y) z
invertOp x = x


||| invert a row operation
||| assuming acting on identity matrix
invertOpIdentity : RowOp r -> (Matrix r r Double -> Matrix r r Double)
invertOpIdentity (Multiply x y) = replaceEntry (x,x) (1/y)
invertOpIdentity (Add x y z) = replaceEntry (x,z) (negate y)
invertOpIdentity swap@(Swap x y) = operate swap
invertOpIdentity Id = id

findLower' : Matrix n n Double -> List (List (RowOp n)) -> (Matrix n n Double)
findLower' m [] = m
findLower' m (x::xs) = let m' = successiveApply (map invertOpIdentity x) m in findLower' m' xs

||| find the lower triangular matrix L in LU decomposition
partial
findLower : Matrix n n Double -> Maybe (Matrix n n Double)
findLower {n} m = if determinant m == 0.0 then Nothing
                  else let (upper, ops) = eliminateAllColumns m
                       in  Just $ findLower' (identityM n) ops

||| find the inverse of an invertible matrix
partial
findInverse : Matrix n n Double -> Maybe (Matrix n n Double)
findInverse {n} m = if determinant m == 0.0 then Nothing
                    else let m' = joinM m (identityM n)
                         in Just $ dropM 0 n (fst (eliminateAllColumns m'))

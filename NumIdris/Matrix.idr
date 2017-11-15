-- ------------------------------------------------------------- [ Matrix.idr ]
-- Module      : NumIdris.Matrix
-- Description : Definitions for matrices
--
-- Part of the code is borrowed from https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Data/Matrix.idr
--------------------------------------------------------------------- [ EOH ]

module NumIdris.Matrix

import Data.Vect as V
import NumIdris.Field
import NumIdris.Vector

%access public export

||| type for a matrix of r rows and c columns, containing data of type t
||| @ r number of rows in the matrix
||| @ c number of columns in the matrix
||| @ t type of the data the matrix contains
Matrix : (Num t, Field t) => (r : Nat) -> (c : Nat) -> (t : Type) -> Type
Matrix r c t = Vect r (Vect c t)

||| get the row of matrix by index
||| @ i index of the row to get
||| @ m the matrix
row : (i : Fin r) -> (m : Matrix r c t) -> Vect c t
row i m = index i m

||| get the column of matrix by index
|||adds two natural numbers| @ j index of the column to get
||| @ m the matrix
column : (j : Fin c) -> (m : Matrix r c t) -> Vect r t
column j m = map (index j) m

||| get an entry at position (i, j) of a matrix
||| @ i index of the row position to get
||| @ j index of the column position to get
||| @ m the matrix
entry : (i : Fin r) -> (j : Fin c) -> (m : Matrix r c t) -> t
entry i j m = (index j . index i) m

||| deleadds two natural numberste a column at a position
||| adds two natural numbers@ j index of the column to delete
||| @ m the matrix
deleteColumnAt : (j : Fin (S c)) -> (m : Matrix r (S c) t) -> Matrix r c t
deleteColumnAt j m = map (deleteAt j) m

||| delete a row at a position
||| @ i index of the row to delete
||| @ m the matrix
deleteRowAt : (i : Fin (S r)) -> (m : Matrix (S r) c t) -> Matrix r c t
deleteRowAt i m = deleteAt i m

||| insert a row to a matrix
||| @ i the index to insert at
||| @ row the new row to insert
||| @ m the original matrix
insertRowAt : (i : Fin (S r)) -> (row : Vect c t) -> (m : Matrix r c t) -> Matrix (S r) c t
insertRowAt i row m = insertAt i row m

||| insert a column to a matrix
||| @ j the index to insert at
||| @ column the new column to insert
||| @ m the original matrix
insertColumnAt : (j : Fin (S c)) -> (column : Vect r t) -> (m : Matrix r c t) -> Matrix  r (S c) t
insertColumnAt j column m = zipWith (insertAt j) column m

||| calculate the submatrix by deleting a row and a column
||| @ i the row to delete
||| @ j the column to delete
||| @ m the matrix to delete from
submatrix: (i : Fin (S r)) -> (j : Fin (S c)) -> (m : Matrix (S r) (S c) t) -> Matrix r c t
submatrix i j m = (deleteRowAt i . deleteColumnAt j) m


||| cofactor expansion along the first column
-- detRec : (Field t) => (m : Matrix (S k) (S k) t) -> t
-- detRec m = entry FZ FZ m
-- detRec (x :: xs) (FS j) = let zipx = (zip x (natRange n)) in
                              -- map (\(xj, j) => let fj = natToFin j
                              --                      sign = if even (1 + nj) then 1 else -1 in
                              -- sign * (entry (FZ) fj)  * detRec (submatrix FZ fj m)) zipx


||| calcuate the determinant of a square matrix
||| @ m the matrix
determinant : (Field t) => (m : Matrix n n t) -> t
determinant Nil = zero
determinant {n = S Z} (x :: xs) = (head x)
determinant {n = S (S Z)} m = let ad = entry FZ FZ m * entry (FS FZ) (FS FZ) m
                                  bc = entry (FS FZ) FZ m * entry FZ (FS FZ) m in
                                  ad - bc
determinant (x :: xs) = ?detRec

||| calculate the trace of a matrix
||| @ m the matrix
trace : (Field t) => (m : Matrix (S n) (S n) t) -> t
trace m = foldl1 (+) (diag m)

-- inverse : (Field t) => (m : Matrix (S n) (S n) t) -> Matrix (S n) (S n) t


||| add two matrices
||| @ m1 the first matrix
||| @ m2 the second matrix
add : (Field t) => (m1 : Matrix r c t) -> (m2 : Matrix r c t) -> Matrix r c t
add = zipWith Vector.add

||| multiply two matrices
||| @ m1 the first matrix
||| @ m2 the second matrix
multiply : (Field t) => (m1: Matrix r c t) -> (m2 : Matrix c r' t) -> Matrix r r' t
multiply m1 m2 = let m2' = transpose m2 in
        map (\row => map(\col => (dot row col)) m2') m1

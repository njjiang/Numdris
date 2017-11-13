-- ------------------------------------------------------------- []
-- Module      :
-- Description :
--
-- Part of the code is borrowed from https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Data/Matrix.idr
--------------------------------------------------------------------- [ EOH ]

module NumIdris.Matrix

import Data.Vect as Vect
import NumIdris.Field
import NumIdris.Vector


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
||| @ j index of the column to get
||| @ m the matrix
column : (j : Fin c) -> (m : Matrix r c t) -> Vect r t
column j m = map (index j) m

||| get an entry at position (i, j) of a matrix
||| @ i index of the row position to get
||| @ j index of the column position to get
||| @ m the matrix
entry : (i : Fin r) -> (j : Fin c) -> (m : Matrix r c t) -> t
entry i j m = (index j . index i) m

||| delete a column at a position
||| @ j index of the column to delete
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


determinant : (Field t) => (m : Matrix r c t) -> t
determinant {r = Z} {c = Z} m = zero
determinant {r = S r} {c = S c} m = ?det


meh : Matrix 2 2 Double
meh = fromList [[3,4], [5,6]]

ex : Matrix 2 2 Integer
ex = fromList [[1,2],[3,4]]

result : Matrix 2 2 Integer
result = fromList [[7, 10], [15, 22]]

add : (Field t) => (m1 : Matrix r c t) -> (m2 : Matrix r c t) -> Matrix r c t
add = zipWith Vector.add

multiply : (Field t) => (m1: Matrix r c t) -> (m2 : Matrix c r' t) -> Matrix r r' t
multiply m1 m2 = let m2' = transpose m2 in
        map (\row => map(\col => (dot row col)) m2') m1

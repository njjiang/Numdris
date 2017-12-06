-- ------------------------------------------------------------- [ Matrix.idr ]
-- Module      : Numdris.Matrix
-- Description : Definitions for matrices
--
-- Part of the code is borrowed from https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Data/Matrix.idr
--------------------------------------------------------------------- [ EOH ]

module Numdris.Matrix

import Data.Vect as V
import Data.Complex as C
import Numdris.Field
import Numdris.Vector

%access public export

||| type for a matrix of r rows and c columns, containing data of type t
||| @ r number of rows in the matrix
||| @ c number of columns in the matrix
||| @ t type of the data the matrix contains
Matrix : (Num t) => (r : Nat) -> (c : Nat) -> (t : Type) -> Type
Matrix r c t = Vect r (Vect c t)

||| get the row of matrix by index
||| @ i index of the row to get
||| @ m the matrix
getRow : (i : Fin r) -> (m : Matrix r c t) -> Vect c t
getRow i m = index i m

||| get the column of matrix by index
|||adds two natural numbers| @ j index of the column to get
||| @ m the matrix
getColumn : (j : Fin c) -> (m : Matrix r c t) -> Vect r t
getColumn j m = map (index j) m

||| get an entry at position (i, j) of a matrix
||| @ i index of the row position to get
||| @ j index of the column position to get
||| @ m the matrix
entry' : (i : Fin r) -> (j : Fin c) -> (m : Matrix r c t) -> t
entry' i j m = (index j . index i) m

||| get an entry at position (i, j) of a matrix
entry : (Fin r, Fin c) -> (m : Matrix r c t) -> t
entry (i,j) m = (index j . index i) m

||| set entry of a matrix to be some element
||| @ m the original matrix
||| @ index the index to be replaced
||| @ elem the new element to replace with
replaceEntry : (index : (Fin r, Fin c)) -> (elem : t) -> (m : Matrix r c t) -> Matrix r c t
replaceEntry (i,j) elem m = let rowi = getRow i m
                                replacej = replaceAt j elem rowi in
                            replaceAt i replacej m


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
submatrix : (i : Fin (S r)) -> (j : Fin (S c)) -> (m : Matrix (S r) (S c) t) -> Matrix r c t
submatrix i j m = (deleteRowAt i . deleteColumnAt j) m

||| get a vector of indices/fins of length n
||| @ n length of the vector
fins : (n : Nat) -> Vect n (Fin n)
fins Z = Nil
fins (S n) = FZ :: map FS (fins n)

||| distribute an element to a vector and get a vector of pairs
distribute : a -> Vect n b -> Vect n (a,b)
distribute elem v = map (\x => (elem, x)) v

-----------------------------------------------------------------------
--                        Special matrices
-----------------------------------------------------------------------

||| get a matrix of indices of a rxc matrix
indicesMatrix : (r : Nat) -> (c : Nat) -> Matrix r c (Fin r, Fin c)
indicesMatrix r c = map (\x => distribute x cfins) rfins where
                    rfins : Vect r (Fin r)
                    rfins = fins r
                    cfins : Vect c (Fin c)
                    cfins = fins c


||| get a list of indices of a rxc matrix
indices : (r : Nat) -> (c : Nat) -> Vect (r*c) (Fin r, Fin c)
indices r c = concat (indicesMatrix r c)

||| map an operation on a matrix
iterateM : (f : t -> t') -> (m : Matrix r c t) -> Matrix r c t'
iterateM f m = map (\row => map f row) m

||| zip two matrices
zipM : Matrix r c a -> Matrix r c b -> Matrix r c (a,b)
zipM m1 m2 = zipWith (zip) m1 m2

||| zip two matrices with some function applied
zipMWith : (a -> b -> t) -> Matrix r c a -> Matrix r c b -> Matrix r c t
zipMWith f m1 m2 = zipWith (zipWith f) m1 m2


||| fill a r x c matrix with some element
fill : (Num t) => (elem :t) -> (r : Nat) -> (c : Nat) -> Matrix r c t
fill elem r c = replicate r (replicate c elem)

||| construct a r x c matrix filled with zero
zerosM : (Num t) => (r : Nat) -> (c : Nat) -> Matrix r c t
zerosM r c = replicate r (Vector.zeros c)

||| construct an n x n identity matrix
identityM : (Num t, Field t) => (n : Nat) -> Matrix n n t
identityM n = zipWith (\i => \row => replaceAt i one row) (fins n) (zerosM n n)

||| construct a r x c matrix with some element at position (i,j) and zero everywhere else
||| @ r number of rows of the matrix
||| @ c number of columns of the matrix
||| @ index index of the specific element
||| @ elem the specific element
EijM : (Num t, Field t) => (r : Nat) -> (c : Nat) -> (index : (Fin r, Fin c)) -> (elem : t)-> Matrix r c t
EijM r c index elem = replaceEntry index elem (zerosM r c)


||| expand a matrix with some padding elements
padM : (Field t) => (m : Matrix r c t) -> (r' : Nat) -> (c' : Nat) -> (elem :t) -> Matrix (r + r') (c + c') t
padM {c} m r' c' elem = let m' = map (\row => pad row elem c') m in
                        m' ++ replicate r' (replicate (c + c') elem)

||| take the upperleft r x c submatrix of matrix m
||| @ m original matrix
||| @ r the number of row in the submatrix
||| @ c the number of column in the submatrix
takeM : (r : Nat) -> (c : Nat) -> (m : Matrix (r + r') (c + c') t) -> Matrix r c t
takeM r c m = take r (map (take c) m)

||| drop the upperleft r x c submatrix of matrix m
||| @ m original matrix
||| @ r the number of row in the submatrix
||| @ c the number of column in the submatrix
dropM : (r : Nat) -> (c : Nat) -> (m : Matrix (r + r') (c + c') t) -> Matrix r' c' t
dropM r c m = drop r (map (drop c) m)


||| helper function for type checking
rewriteSingleton : Vect (1*c) t -> Vect c t
rewriteSingleton {c} v = rewrite sym $ multOneLeftNeutral c in v

||| split a vector of r*c size to a r x c matrix
splitVect : (r : Nat) -> (c : Nat) -> (v : Vect (r * c) t) ->  Matrix r c t
splitVect (S Z) c v = [(rewriteSingleton v)]
splitVect (S r) c v = (take c v) :: splitVect r c (drop c v)

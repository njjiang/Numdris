-- ------------------------------------------------------------- [ Matrix.idr ]
-- Module      : NumIdris.Matrix
-- Description : Definitions for matrices
--
-- Part of the code is borrowed from https://github.com/idris-lang/Idris-dev/blob/master/libs/contrib/Data/Matrix.idr
--------------------------------------------------------------------- [ EOH ]

module NumIdris.Matrix

import Data.Vect as V
import Data.Complex as C
import NumIdris.Field
import NumIdris.Vector

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

entryIndex : Eq t => t -> Matrix r c t -> Maybe (Fin r, Fin c)
entryIndex e m = ?entryIndex_rhs

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

||| get a list of indices
indices : (r : Nat) -> (c : Nat) -> Vect (r*c) (Fin r, Fin c)
indices r c = concat indicesMatrix where
              rfins : Vect r (Fin r)
              rfins = fins r
              cfins : Vect c (Fin c)
              cfins = fins c
              distribute : Fin r -> Vect n (Fin c) -> Vect n (Fin r, Fin c)
              distribute elem v = map (\x => (elem, x)) v
              indicesMatrix : Matrix r c (Fin r ,Fin c)
              indicesMatrix = map (\x => distribute x cfins) rfins


iterateM : (f : t -> t') -> (m : Matrix r c t) -> Matrix r c t'
iterateM f m = map (\row => map f row) m

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
determinant {n = S (S Z)} m = let ad = entry (FZ   , FZ) m * entry (FS FZ, FS FZ) m
                                  bc = entry (FS FZ, FZ) m * entry (FZ   , FS FZ) m in
                                  ad - bc
determinant (x :: xs) = ?detRec_rhs

||| calculate the trace of a matrix
||| @ m the matrix
trace : (Field t) => (m : Matrix (S n) (S n) t) -> t
trace m = foldl1 (+) (diag m)

||| calculate the inverse of a matrix
inverse : (Field t) => (m : Matrix (S n) (S n) t) -> Matrix (S n) (S n) t
inverse = ?inverse_rhs


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



||| get the max element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
maxAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
maxAlongRow m row = Vector.max $ getRow row m

||| get the min element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
minAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
minAlongRow m row = Vector.min $ getRow row m

||| get the max element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
maxAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
maxAlongColumn m col = Vector.max $ getColumn col m

||| get the min element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
minAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
minAlongColumn m col = Vector.min $ getColumn col m

||| get the argmax element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
argmaxAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> (Fin (S r), Fin (S c))
argmaxAlongRow m row = let col = Vector.argmax $ getRow row m in
                       (row, col)
||| get the argmin element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
argminAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> (Fin (S r), Fin (S c))
argminAlongRow m row = let col = Vector.argmin $ getRow row m in
                       (row, col)

||| get the argmax element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
argmaxAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> (Fin (S r), Fin (S c))
argmaxAlongColumn m col = let row = Vector.argmax $ getColumn col m in
                              (row, col)

||| get the argmin element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
argminAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> (Fin (S r), Fin (S c))
argminAlongColumn m col = let row = Vector.argmin $ getColumn col m in
                          (row, col)

||| sum along row
sumAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
sumAlongRow m row = Vector.sum $ getRow row m

||| product along column
sumAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
sumAlongColumn m col = Vector.sum $ getColumn col m

||| product along row
productAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
productAlongRow m row = Vector.product $ getRow row m

||| product along column
productAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
productAlongColumn m col = Vector.product $ getColumn col m

||| flatten a r x c matrix to a vector of length r * c
flatten : (Field t) => (m : Matrix r c t) -> Vect (r * c) t
flatten m = concat m

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

||| standard basis of a matrix
basis : (Field t, Num t) => (m : Matrix r c t) -> Vect (r * c) (Matrix r c t)
basis {r} {c} m = map (\ij => EijM r c ij one) (indices r c)

-- clipping, vector and matrix


-----------------------------------------------------------------------
--                        Complex field operations
-----------------------------------------------------------------------

real : Num t => (m : Matrix r c (Complex t)) -> Matrix r c t
real m = iterateM C.realPart m

imaginary : Num t => (m : Matrix r c (Complex t)) -> Matrix r c t
imaginary m = iterateM C.imagPart m

conjugate : (Neg t, Num t) => (m : Matrix r c (Complex t)) -> Matrix r c (Complex t)
conjugate m = iterateM C.conjugate m

conjugateTranspose : (Neg t, Num t) => (m : Matrix r c (Complex t)) -> Matrix c r (Complex t)
conjugateTranspose m = conjugate $ transpose m

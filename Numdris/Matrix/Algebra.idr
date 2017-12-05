-- ------------------------------------------------------------- [ Algebra.idr ]
-- Module      : Numdris.Matrix.Algebra
-- Description : Definitions for matrices
--
--------------------------------------------------------------------- [ EOH ]

module Numdris.Matrix.Algebra

import Numdris.Matrix



||| Num instance for Matrix
[MatrixNum] (Field t, Num t) => Num (Matrix r c t) where
    (+) = Matrix.add
    (*) = zipMWith (*)
    fromInteger x {r} {c} = replicate r $ replicate c (fromInteger x)


||| Neg instance for Matrix
[MatrixNeg] (Field t, Neg t) => Neg (Matrix r c t) where
    (-) = zipMWith (-)
    abs = iterateM abs
    negate = iterateM negate

||| Ord instance for Matrix
||| lexicographical order
[MatrixOrd] (Field t, Ord t) => Ord (Matrix r c t) where
    compare [] [] = EQ
    compare (x::xs) (y::ys) = case compare x y of
                              EQ => compare xs ys
                              _ => compare x y




||| sum a vector while alternating between (+) and (-) for each element
alternateSum : (Num t, Neg t) => Vect n t -> t
alternateSum [] = 0
alternateSum [x] = x
alternateSum (x::y::xs) = x - y + (alternateSum xs)


||| calcuate the determinant of a square matrix
||| @ m a square matrix
determinant : (Field t) => (m : Matrix n n t) -> t
determinant Nil = zero
determinant {n = S Z} [[x]] = x
determinant {n = S (S Z)} m = let ad = entry (FZ   , FZ) m * entry (FS FZ, FS FZ) m
                                  bc = entry (FS FZ, FZ) m * entry (FZ   , FS FZ) m in
                                  ad - bc
determinant {n = S len} m@(x :: xs) = let n = S len
                                          subs = map (\j => submatrix (FZ) j m) (fins n)
                                          in alternateSum (zipWith (*) x (map determinant subs))

||| calculate the trace of a matrix
||| @ m a square matrix
trace : (Field t) => (m : Matrix (S n) (S n) t) -> t
trace m = foldl1 (+) (diag m)


||| add two matrices
||| @ m1 the first matrix
||| @ m2 the second matrix
add : (Field t) => (m1 : Matrix r c t) -> (m2 : Matrix r c t) -> Matrix r c t
add = zipWith Vector.add

||| multiply two matrices
multiply : (Field t) => Matrix r c t -> Matrix c r' t -> Matrix r r' t
multiply m1 m2 = let m2' = transpose m2 in
        map (\row => map(\col => (dot row col)) m2') m1


||| mua matrix by a column vector
multiplyVect : (Field t) => Matrix r c t -> Vect c t -> Vect r t
multiplyVect m v = map (Vector.dot v) m

||| flatten a r x c matrix to a vector of length r * c
flatten : (Field t) => (m : Matrix r c t) -> Vect (r * c) t
flatten m = concat m

submatrices : (m : Matrix (S n) (S n) t) -> Matrix (S n) (S n) (Matrix n n t)
submatrices {n} m = let indices = indicesMatrix (S n) (S n)
                    in iterateM (\(i,j) => submatrix i j m) indices



||| standard basis of a matrix
basis : (Field t, Num t) => (m : Matrix r c t) -> Vect (r * c) (Matrix r c t)
basis {r} {c} m = map (\ij => EijM r c ij one) (indices r c)


-----------------------------------------------------------------------
--                        inverse
-----------------------------------------------------------------------

||| a cofactor row starting with 1 of some length
||| [1, -1, 1, -1 ....]
cofactorOddRow : (Num t, Neg t) => (len : Nat) -> Vect len t
cofactorOddRow Z = []
cofactorOddRow (S Z) = [1]
cofactorOddRow (S (S n)) = [1, -1] ++ cofactorOddRow n

||| a cofactor r x c matrix
||| for each position (i,j), Mij = 1 if (i+j) is even, else Mij = -1
cofactorMatrix : (Num t, Neg t) => (r : Nat) -> (c : Nat) -> Matrix r c t
cofactorMatrix r c = zipWith (scale) (cofactorOddRow r) (replicate r (cofactorOddRow c))

minors : (Field t) => (m : Matrix (S n) (S n) t) -> Matrix (S n) (S n) t
minors {n} m = let indices = indicesMatrix (S n) (S n)
               in iterateM (\(i,j) => determinant $ submatrix i j m) indices

||| calculate the inverse of a matrix
inverse : (Fractional t, Field t) => (m : Matrix (S n) (S n) t) -> Matrix (S n) (S n) t
inverse {n} m = let det = determinant m
                    transposeCofactor = Vect.transpose (zipMWith (*) (minors m) (cofactorMatrix (S n) (S n)))
                    in iterateM (* (1/det)) transposeCofactor

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

-----------------------------------------------------------------------
--                        Eigen decompositions
-----------------------------------------------------------------------

||| compute the corresponding eigenvalue t given an eigenvector of a matrix
||| (A-tI)x = 0
eigenvalue : Matrix n n Double -> (eigenvector : Vect n Double) -> Double
-- eigenvalue A x = divide (multiplyVect A x) x


-----------------------------------------------------------------------
--                        Min/Max/Sum/Prod
-----------------------------------------------------------------------


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

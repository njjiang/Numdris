-- ------------------------------------------------------------- [ Algebra.idr ]
-- Module      : Numdris.Matrix.Algebra
-- Description : Definitions for matrices
--------------------------------------------------------------------- [ EOH ]

module Numdris.Matrix.Algebra

import Data.Vect
import Data.Complex
import Numdris.Vect.Util
import Numdris.Matrix
import Numdris.Field
import Effects
import Effect.Random
import Effect.System

%access public export

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
addM : (Field t) => (m1 : Matrix r c t) -> (m2 : Matrix r c t) -> Matrix r c t
addM = zipWith add

||| multiply two matrices
multiplyM : (Field t) => Matrix r c t -> Matrix c r' t -> Matrix r r' t
multiplyM m1 m2 = let m2' = transpose m2 in
                  map (\row => map(\col => (dot row col)) m2') m1


||| mua matrix by a column vector
multiplyVect : (Field t) => Matrix r c t -> Vect c t -> Vect r t
multiplyVect m v = map (dot v) m

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
inverse : (Fractional t, Field t) => (m : Matrix (S n) (S n) t) -> Maybe (Matrix (S n) (S n) t)
inverse {n} m = if determinant m == zero then Nothing
                else let det = determinant m
                         transposeCofactor = Vect.transpose (zipMWith (*) (minors m) (cofactorMatrix (S n) (S n)))
                     in Just $ iterateM (* (1/det)) transposeCofactor


-----------------------------------------------------------------------
--                        Complex field operations
-----------------------------------------------------------------------

real : Num t => (m : Matrix r c (Complex t)) -> Matrix r c t
real m = iterateM realPart m

imaginary : Num t => (m : Matrix r c (Complex t)) -> Matrix r c t
imaginary m = iterateM imagPart m

conjugate : (Neg t, Num t) => (m : Matrix r c (Complex t)) -> Matrix r c (Complex t)
conjugate m = iterateM conjugate m

conjugateTranspose : (Neg t, Num t) => (m : Matrix r c (Complex t)) -> Matrix c r (Complex t)
conjugateTranspose m = conjugate $ transpose m

-----------------------------------------------------------------------
--                        Eigen decompositions
-- borrowed from https://gist.github.com/justinmanley/f2e169feb32e06e06c2f
-----------------------------------------------------------------------

eigenvalue : Matrix n n Double -> Vect n Double -> Double
eigenvalue m v = dot v (multiplyVect m v)


||| estimate the eigenvector of a matrix
eigenvector : Matrix n n Double -> (precision : Double) -> (seed : Vect n Double) -> List (Vect n Double) -> Vect n Double
eigenvector A precision seed previous {n} = if err < precision
                                        then result
                                        else eigenvector A precision result previous where
                                        result' : Vect n Double
                                        result' = (orthorgonalizeAll {len=n}) seed previous
                                        result : Vect n Double
                                        result = normalize $ multiplyVect A result'
                                        err : Double
                                        err = case compare (eigenvalue A result) 0 of
                                              GT => norm (subtract result' result)
                                              LT => norm (add result' result)


||| generate a random double between 0 and 1
rndDouble : Integer -> Eff Double [RND]
rndDouble max = do
                rnd <- rndInt 0 max
                pure (fromInteger rnd / fromInteger max)


||| map using a function which depends on the previously-mapped values.
||| like a combination of map and fold in which the state is the values
||| which have already been mapped.
mapRemember : (a -> List b -> b) -> List a -> List b -> List b
mapRemember f values state = case values of
                             []        => reverse state
                             (x :: xs) => mapRemember f xs (f x state :: state)


||| compute the eigenvectors
eigenvectors : Matrix n n Double -> (precision : Double) -> Eff (List (Vect n Double)) [RND, SYSTEM]
eigenvectors {n} matrix precision = do
    srand !time
    seedVectors <- mapE (\vs => mapVE (\x => rndDouble x) vs) $ List.replicate n (Vect.replicate n (cast $ 1 / precision))
    pure $ mapRemember (eigenvector matrix precision) seedVectors []

-----------------------------------------------------------------------
--                        Min/Max/Sum/Prod
-----------------------------------------------------------------------

||| get the max element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
maxAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
maxAlongRow m row = max $ getRow row m

||| get the min element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
minAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
minAlongRow m row = min $ getRow row m

||| get the max element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
maxAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
maxAlongColumn m col = max $ getColumn col m

||| get the min element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
minAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
minAlongColumn m col = min $ getColumn col m

||| get the argmax element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
argmaxAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> (Fin (S r), Fin (S c))
argmaxAlongRow m row = let col = argmax $ getRow row m in
                       (row, col)
||| get the argmin element along a row in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ row the index of the row
argminAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> (Fin (S r), Fin (S c))
argminAlongRow m row = let col = argmin $ getRow row m in
                       (row, col)

||| get the argmax element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
argmaxAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> (Fin (S r), Fin (S c))
argmaxAlongColumn m col = let row = argmax $ getColumn col m in
                              (row, col)

||| get the argmin element along a column in a matrix
||| undefined for empty matrix
||| @ m the matrix
||| @ col the index of the column
argminAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> (Fin (S r), Fin (S c))
argminAlongColumn m col = let row = argmin $ getColumn col m in
                          (row, col)

||| sum along row
sumAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
sumAlongRow m row = Util.sum $ getRow row m

||| sum along column
sumAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
sumAlongColumn m col = Util.sum $ getColumn col m

||| product along row
productAlongRow : (Field t) => (m : Matrix (S r) (S c) t) -> (row : Fin (S r)) -> t
productAlongRow m row = Util.product $ getRow row m

||| product along column
productAlongColumn : (Field t) => (m : Matrix (S r) (S c) t) -> (col : Fin (S c)) -> t
productAlongColumn m col = Util.product $ getColumn col m



||| Num instance for Matrix
[MatrixNum] (Field t, Num t) => Num (Matrix r c t) where
    (+) = addM
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


-- [MatrixEq] (Field t, Eq t) => Eq (Matrix r c t) where
--     (==) = \m1 => \m2 => case compare @{MatrixOrd} m1 m2 of
--                          EQ => True
--                          _ => False

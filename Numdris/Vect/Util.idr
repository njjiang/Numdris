-- ------------------------------------------------------------- [ Util.idr ]
-- Module      : Numdris.Vect.Util
-- Description : some basic vector operations
--------------------------------------------------------------------- [ EOH ]
module Numdris.Vect.Util

import Data.Vect as Vect
import Numdris.Field

%access public export

||| initialize a vector of some length filled with some element
||| @ len length of the vector to initialize
||| @ initElem the initial element
initVector : (len : Nat) -> (initElem : t) -> Vect len t
initVector Z _ = Nil
initVector (S n) initElem = initElem :: initVector n initElem

Num t => Num (Vect len t) where
    (+) = zipWith (+)
    (*) = zipWith (*)
    fromInteger x = replicate _ (fromInteger x)

Neg t => Neg (Vect len t) where
    (-) = zipWith (-)
    negate = map negate


Cast (Vect n Int) (Vect n Double) where
     cast = map (cast {to=Double})

Cast (Vect n Nat) (Vect n Double) where
     cast = map (cast {to=Double})

||| initialize a vector of some length filled with zeros
||| @ len length of the vector to initialize
zeros : (Num t) => (len : Nat) -> Vect len t
zeros len = initVector len 0

||| initialize a vector of some length filled with ones
||| @ len length of the vector to initialize
ones : (Num t) => (len : Nat) -> Vect len t
ones len = initVector len 1

arangelist : (Ord t, Num t) => (start : t) -> (end : t) -> (step : t) -> List t
arangelist start end step = if start >= end then []
                            else start :: (arangelist (start+step) end step)

||| initialize a vector filled with data from start up to end, each differ by step
||| @ start the start of the range
||| @ end the end of the range
||| @ step the difference between two elementadds two natural numberss
arange : (Ord t, Num t) => (start : t) -> (end : t) -> (step : t) -> (p : Nat ** Vect p t)
arange start end step = (_ ** fromList (arangelist start end step))

natRangeVect : (n : Nat) -> Vect n Nat
natRangeVect Z = []
natRangeVect (S n) with (natRangeVect n)
    | xx = insertAt (fromMaybe FZ $ natToFin n (S n)) n xx

||| multiply a vector by some scalar
||| @ c scalar
||| @ v the vector
scale : (Num t) => (c : t) -> (v : Vect len t) -> Vect len t
scale c v = map (* c) v

||| add two vectors together
||| @ v1 first vector
||| @ v2 second vector
add : (Num t) => (v1 : Vect len t) -> (v2 : Vect len t) -> Vect len t
add v1 v2 = zipWith (+) v1 v2


||| v1 - v2
subtract : (Neg t) => Vect len t -> Vect len t -> Vect len t
subtract v1 v2 = zipWith (-) v1 v2


||| compute pointwise v1 / v2
divide : (v1 : Vect len Double) -> (v2 : Vect len Double) -> Vect len Double
divide = zipWith (/)


||| find the max element in some non-empty vector
||| @ v the vector
max : (Ord t) => (v : Vect (S n) t) -> t
max v = foldl1 max v

||| find the min element in some non-empty vector
||| @ v the vector
min : (Ord t) => (v : Vect (S n) t) -> t
min v = foldl1 min v

||| find the index of the max element in some non-empty vector
||| @ v the vector
argmax : (Ord t) => (v : Vect (S n) t) -> Fin (S n)
argmax v = let m = max v in
           fromMaybe (FZ) (elemIndex m v)

||| find the index of the min element in some non-empty vector
||| @ v the vector
argmin : (Ord t) => (v : Vect (S n) t) -> Fin (S n)
argmin v = let m = min v in
           fromMaybe (FZ) (elemIndex m v)

||| take the inner/dot product of two vectors
||| @ v1 first vector
||| @ v2 second vector
dot : (Num t) => (v1 : Vect len t) -> (v2 : Vect len t) -> t
dot v1 v2 = foldr (+) 0 (Vect.zipWith (*) v1 v2)

inner : (Num t) => (v1 : Vect len t) -> (v2 : Vect len t) -> t
inner = dot

||| take the outer product of two vectors
||| @ v1 first vector
||| @ v2 second vector
outer : (Num t, Field t) => (v1 : Vect len1 t) -> (v2 : Vect len2 t) -> Vect len1 (Vect len2 t)
outer v1 v2 = map (\x => map (* x) v2) v1

||| transpose a column vector to a row vector
||| @ v the column vector
transpose : (Num t) => (v : Vect len t) -> Vect len (Vect 1 t)
transpose v = map (\x => [x]) v


||| calculate the sum of a vector
||| @ v the vector
sum : (Num t) => (v : Vect len t) -> t
sum {len = Z}   v = 0
sum {len = S _} v = foldl1 (+) v

||| calculate the product of a vector
||| @ v the vector
product : (Num t) => (v : Vect len t) -> t
product {len = Z}   v = 0
product {len = S _} v = foldl1 (*) v

||| pad a vector with some element for some length at the end
||| @ v original vector
||| @ elem the element to pad with
||| @ padLen the length of padding
pad : (Num t) => (v : Vect len t) -> (elem : t) -> (padLen : Nat) -> Vect (len + padLen) t
pad v elem padLen = v ++ (replicate padLen elem)

||| calculate the mean of an nonempty vector
mean : (v : Vect (S n) Double) -> Double
mean {n} v =  (Util.sum v) / (cast {to=Double} (S n))

||| compute the norm/length of a vector
norm : Vect len Double -> Double
norm v = sqrt (dot v v)

||| normalize a vector
normalize : Vect len Double -> Vect len Double
normalize v = scale (1/(norm v)) v

||| make two vectors orthorgonal
||| w - v (v dot w)/(v dot v)
orthorgonalize : Vect len Double -> Vect len Double -> Vect len Double
orthorgonalize v w = w `subtract` (scale ((dot v w)/(dot v v)) v)

||| make the current vector orthorgonalize to a list of vectors
orthorgonalizeAll : Vect len Double -> List (Vect len Double) -> Vect len Double
orthorgonalizeAll v vs = foldl orthorgonalize v vs


||| get a vector of indices/fins of length n
||| @ n length of the vector
fins : (n : Nat) -> Vect n (Fin n)
fins Z = Nil
fins (S n) = FZ :: map FS (fins n)

indexed : Vect n t -> Vect n (Fin n, t)
indexed {n} v = zip (fins n) v

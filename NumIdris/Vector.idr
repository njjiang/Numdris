-- ------------------------------------------------------------- [ Vector.idr ]
-- Module      : NumIdris.Vector
-- Description : some basic vector operations
--------------------------------------------------------------------- [ EOH ]
module NumIdris.Vector

import Data.Vect as Vect
import NumIdris.Field

%access public export

||| initialize a vector of some length filled with some element
||| @ len length of the vector to initialize
||| @ initElem the initial element
initVector : (Field t, Num t) => (len : Nat) -> (initElem : t) -> Vect len t
initVector Z _ = Nil
initVector (S n) initElem = initElem :: initVector n initElem

||| initialize a vector of some length filled with zeros
||| @ len length of the vector to initialize
zeros : (Field t, Num t) => (len : Nat) -> Vect len t
zeros len = initVector len zero

||| initialize a vector of some length filled with ones
||| @ len length of the vector to initialize
ones : (Field t, Num t) => (len : Nat) -> Vect len t
ones len = initVector len one

arangelist : (Field t) => (start : t) -> (end : t) -> (step : t) -> List t
arangelist start end step = if start >= end then []
                            else start :: (arangelist (start+step) end step)

||| initialize a vector filled with data from start up to end, each differ by step
||| @ start the start of the range
||| @ end the end of the range
||| @ step the difference between two elementadds two natural numberss
arange : (Field t) => (start : t) -> (end : t) -> (step : t) -> (p : Nat ** Vect p t)
arange start end step = (_ ** fromList (arangelist start end step))

||| multiply a vector by some scalar
||| @ c scalar
||| @ v the vector
scale : (Field t) => (c : t) -> (v : Vect len t) -> Vect len t
scale c v = map (* c) v

||| add two vectors together
||| @ v1 first vector
||| @ v2 second vector
add : (Num t, Field t) => (v1 : Vect len t) -> (v2 : Vect len t) -> Vect len t
add v1 v2 = zipWith (+) v1 v2

||| find the max element in some non-empty vector
||| @ v the vector
max : (Ord t, Field t) => (v : Vect (S n) t) -> t
max v = foldl1 max v

||| find the min element in some non-empty vector
||| @ v the vector
min : (Ord t, Field t) => (v : Vect (S n) t) -> t
min v = foldl1 min v

||| find the index of the max element in some non-empty vector
||| @ v the vector
argmax : (Ord t, Field t) => (v : Vect (S n) t) -> Fin (S n)
argmax v = let m = max v in
           fromMaybe (FZ) (elemIndex m v)

||| find the index of the min element in some non-empty vector
||| @ v the vector
argmin : (Ord t, Field t) => (v : Vect (S n) t) -> Fin (S n)
argmin v = let m = min v in
           fromMaybe (FZ) (elemIndex m v)

||| take the inner/dot product of two vectors
||| @ v1 first vector
||| @ v2 second vector
dot : (Num t, Field t) => (v1 : Vect len t) -> (v2 : Vect len t) -> t
dot v1 v2 = foldr (+) 0 (Vect.zipWith (*) v1 v2)

inner : (Num t, Field t) => (v1 : Vect len t) -> (v2 : Vect len t) -> t
inner = dot

-- ||| take the outer product of two vectors
-- ||| @ v1 first vector
-- ||| @ v2 second vector
-- outer : (Num t, Field t) => (v1 : Vect len1 t) -> (v2 : Vect len2 t) -> Vect len1 (Vect len2 t)
-- outer v1 v2 = map (\x => map (* x) v2) v1

||| transpose a column vector to a row vector
||| @ v the column vector
transpose : (Num t, Field t) => (v : Vect len t) -> Vect len (Vect 1 t)
transpose v = map (\x => [x]) v

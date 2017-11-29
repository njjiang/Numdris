-- ------------------------------------------------------------- [ Tensor.idr ]
-- Module      : NumIdris.NDVect
-- Description : n-dimensional vector definitions and operations
--------------------------------------------------------------------- [ EOH ]

module NumIdris.Tensor

import Data.Vect
import Data.Complex
import NumIdris.Vector
import NumIdris.Matrix

%access public export

||| n-dimensional vector of with rank and shape encoded in types
NDVect : (Num t) => (rank : Nat) -> (shape : Vect rank Nat) -> (t : Type) -> Type
NDVect Z     []      t = t
NDVect (S n) (x::xs) t = Vect x (NDVect n xs t)


||| select the i-th dimension of a n-dimensional vector
||| @ i the dimension to select
||| @ v the n-dimensional vector
select : (i : Fin rank) -> (v : NDVect rank shape t) -> Vect (Vect.index i shape) t

||| iterate through a tensor
iterateT : (f : t -> t') -> (v : NDVect r s t) -> NDVect r s t'
iterateT {r = Z}   {s = []}    f v = f v
iterateT {r = S Z} {s = [x]}   f v = map f v
iterateT {r = S n} {s = x::xs} f v = map (iterateT f) v



||| multiply a tensor by a scalar
||| @ c scalar
||| @ v tensor
||| note: there seems to be a compiler bug that such that calling iterateT does not type check
scale : Num t => (c : t) -> (v : NDVect rank shape t) -> NDVect rank shape t
scale {rank = Z}   {shape = []}    c v = c * v
scale {rank = S Z} {shape = [x]}   c v = map (* c) v
scale {rank = S n} {shape = x::xs} c v = map (Tensor.scale c) v


||| computes the outer product of two tensors
outerProd : Num t => (v: NDVect r shape t) -> (w: NDVect r' shape' t) -> NDVect (r + r') (shape ++ shape') t
outerProd {r = Z}   {shape = []}    v w = scale v w
outerProd {r = S n}  {shape = x::xs} v w = map (\x => outerProd x w) v

-- sum
-- inner product

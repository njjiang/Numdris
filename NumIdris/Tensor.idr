-- ------------------------------------------------------------- [ Tensor.idr ]
-- Module      : NumIdris.Tensor
-- Description : tensor definitions
--------------------------------------------------------------------- [ EOH ]

module NumIdris.Tensor

import NumIdris.Field
import Data.Vect
import NumIdris.Vector


||| Tensors as n-dimensional array
Tensor : (Num t, Field t) => Vect n Nat -> (t : Type) -> Type

||| Scalar as 0-dimensional array
Scalar : (Num t, Field t) => (t : Type) -> Tensor [] t

||| multi dimensional tensor
Dimensional : (Field t) => Vect n (Tensor d t) -> Tensor (n::d) t

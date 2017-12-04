import Data.Vect

||| n-dimensional vector of with rank and shape encoded in types
NDVect : (Num t) => (rank : Nat) -> (shape : Vect rank Nat) -> (t : Type) -> Type
NDVect Z     []      t = t
NDVect (S n) (x::xs) t = Vect x (NDVect n xs t)

||| map an operation on every entry of a tensor
mapT : (f : t -> t') -> (v : NDVect r s t) -> NDVect r s t'
mapT {r = Z}   {s = []}    f v = f v
mapT {r = S Z} {s = [x]}   f v = map f v
mapT {r = S n} {s = x::xs} f v = map (mapT f) v

||| multiply a tensor by a scalar
||| @ c scalar
||| @ v tensor
scale : Num t => (c : t) -> (v : NDVect rank shape t) -> NDVect rank shape t
scale c v = mapT (*c) v -- does not compile

-- `-- ./NumIdris/foo.idr line 18 col 17:
--     When checking right hand side of scale with expected type
--             NDVect rank shape t
--
--     When checking argument v to function Main.mapT:
--             Type mismatch between
--                     NDVect rank shape t (Type of v)
--             and
--                     NDVect r s t (Expected type)
--
--             Specifically:
--                     Type mismatch between
--                             NDVect rank shape t
--                     and
--                             NDVect r s t
--
--

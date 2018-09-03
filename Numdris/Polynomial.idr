-- ------------------------------------------------------------- [ Polynomial.idr ]
-- Module      : Numdris.Polynomial
-- Description : Definitions for polynomials
-- inspired by https://hackage.haskell.org/package/polynomial
--------------------------------------------------------------------- [ EOH ]

module Numdris.Polynomial

import Data.Complex

%access public export

||| Polynomial type
||| head of the coefficients is the constant term
||| we only work with coefficients of type Double
record Polynomial where
       constructor WithCoefficients
       coefficients : List Double

Show Polynomial where
     show (WithCoefficients []) = "0"
     show (WithCoefficients coeff) = showPolynomial $ filter (\(n,c) => c /= 0.0)(zip (natRange (length coeff)) coeff) where
                                     showTerm : (Nat, Double) -> String
                                     showTerm (Z, c) = show c
                                     showTerm (n, c) = let scale = if (c == 1.0) then "" else show c
                                                           n'    = if n == 1 then "" else "^" ++ (show n)
                                                         in scale ++ "x" ++ n'
                                     showPolynomial c = concat $ intersperse " + " (map showTerm c)

zipWithExtend : (a -> a -> a) -> List a -> List a -> List a
zipWithExtend f xx [] = xx
zipWithExtend f [] yy = yy
zipWithExtend f (x::xs) (y::ys) = f x y :: zipWithExtend f xs ys


||| trim the trailing zero coefficients
trim : Polynomial -> Polynomial
trim (WithCoefficients coeff) = WithCoefficients $ reverse $ dropWhile (== 0.0) (reverse coeff)

||| generalize operations on polynomials
zipWithP : (op : Double -> Double -> Double) -> Polynomial -> Polynomial -> Polynomial
zipWithP op f g = WithCoefficients $ zipWithExtend op (coefficients f) (coefficients g)

||| map an operation on each element of a polynomial
mapP : (f : Double -> Double) -> Polynomial -> Polynomial
mapP f (WithCoefficients c) = WithCoefficients $ map f c

||| add two polynomials
add : Polynomial -> Polynomial -> Polynomial
add = zipWithP (+)

||| add two polynomials
subtract : Polynomial -> Polynomial -> Polynomial
subtract f g = add f (mapP negate g)

indexedList : List t -> List (Nat, t)
indexedList l = zip (natRange (length l)) l

multiplyImpl : List Double -> List Double -> List Double
multiplyImpl x y = foldl (zipWithExtend (+)) [] distributey'
                 where
                 y' : List (Nat, Double)
                 y' = indexedList y
                 distributey' : List (List Double)
                 distributey' = map (\(n, v) => (replicate n 0.0) ++ map (*v) x) y'


||| multiply two polynomials
multiply : Polynomial -> Polynomial -> Polynomial
multiply x y = let (WithCoefficients c1) = trim x
                   (WithCoefficients c2) = trim y in
                   WithCoefficients $ multiplyImpl c1 c2


||| degree of the polynomial
degree : Polynomial -> Nat
degree p with (trim p)
    | WithCoefficients coeff = pred (length coeff)


||| check if a polynomial is null
isNull : Polynomial -> Bool
isNull (WithCoefficients coeff) = 0 == (length coeff)

||| computes the value of a polynomialnomial function
||| @ f polynomial
||| @ x value of the variable
eval : (f : Polynomial) -> (x : Double) -> Double
eval (WithCoefficients []) _ = 0.0
eval f x = let coeff = coefficients f
               xpow = map (pow x) (natRange (length coeff))
               in foldl1 (+) (zipWith (*) coeff xpow)

differentiate : Polynomial -> Polynomial
differentiate (WithCoefficients c) = case c' of
                                     Nil => WithCoefficients []
                                     (x::xs) => WithCoefficients xs
                                   where
                                   indexedc : List (Nat, Double)
                                   indexedc = indexedList c
                                   diff : (Nat, Double) -> Double
                                   diff (i,v) = (cast {to=Double} i)*v
                                   c' : List Double
                                   c' = map diff indexedc


integrate : Polynomial -> Polynomial
integrate (WithCoefficients c) = WithCoefficients $ 0 :: map integrate' indexedc
                                 where
                                 integrate' : (Nat, Double) -> Double
                                 integrate' (i,v) = let di = cast {to=Double} i in v/(di+1)
                                 indexedc : List (Nat, Double)
                                 indexedc = indexedList c


Num Polynomial where
    (+) = add
    (*) = multiply
    fromInteger x = let x' = (cast {to=Double} x) in WithCoefficients [x']

Neg Polynomial where
    (-) = subtract
    negate = mapP negate

Abs Polynomial where
    abs = mapP abs

Eq Polynomial where
   (==) x y = let (WithCoefficients c1) = trim x
                  (WithCoefficients c2) = trim y in
                  c1 == c2

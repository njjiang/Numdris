-- ------------------------------------------------------------- [ Polynomial.idr ]
-- Module      : NumIdris.Polynomial
-- Description : Definitions for polynomials
-- inspired by https://hackage.haskell.org/package/polynomial
--------------------------------------------------------------------- [ EOH ]

module NumIdris.Polynomial

import Data.Vect

%access public export

||| Polynomial type
||| head of the coefficients is the constant term
||| we only work with coefficients of type Double
record Polynomial where
       constructor withCoefficients
       coefficients : List Double

Show Polynomial where
     show (withCoefficients []) = "0"
     show (withCoefficients coeff) = showPolynomial $ filter (\(n,c) => c /= 0.0)(zip (natRange (length coeff)) coeff) where
                                     showTerm : (Nat, Double) -> String
                                     showTerm (Z, c) = show c
                                     showTerm (n, c) = let scale = if (c == 1.0) then "" else show c
                                                           n'    = if n == 1 then "" else "^" ++ (show n)
                                                         in scale ++ "x" ++ n'
                                     showPolynomial c = concat $ intersperse " + " (map showTerm c)

Eq Polynomial where
    (==) = \(withCoefficients c1) =>
           \(withCoefficients c2) =>
           (c1 == c2)




zipWithExtend : (a -> a -> a) -> List a -> List a -> List a
zipWithExtend f xx [] = xx
zipWithExtend f [] yy = yy
zipWithExtend f (x::xs) (y::ys) = f x y :: zipWithExtend f xs ys

||| generalize operations on polynomials
zipWithP : (op : Double -> Double -> Double) -> Polynomial -> Polynomial -> Polynomial
zipWithP op f g = withCoefficients $ zipWithExtend op (coefficients f) (coefficients g)

mapP : (f : Double -> Double) -> Polynomial -> Polynomial
mapP f (withCoefficients c) = withCoefficients $ map f c

||| add two polynomials
add : Polynomial -> Polynomial -> Polynomial
add = zipWithP (+)

||| add two polynomials
subtract : Polynomial -> Polynomial -> Polynomial
subtract f g = add f (mapP negate g)

multiply : Polynomial -> Polynomial -> Polynomial

||| trim the trailing zero coefficients
trim : Polynomial -> Polynomial
trim (withCoefficients coeff) = withCoefficients $ reverse $ dropWhile (== 0.0) (reverse coeff)


||| degree of the polynomial
degree : Polynomial -> Nat
degree p with (trim p)
    | withCoefficients coeff = pred (length coeff)


||| check if a polynomial is null
isNull : Polynomial -> Bool
isNull (withCoefficients coeff) = 0 == (length coeff)

||| computes the value of a polynomialnomial function
||| @ f polynomial
||| @ x value of the variable
eval : (f : Polynomial) -> (x : Double) -> Double
eval (withCoefficients []) _ = 0.0
eval f x = let coeff = coefficients f
               xpow = map (pow x) (natRange (length coeff))
               in foldl1 (+) (zipWith (*) coeff xpow)


test : Polynomial
test = withCoefficients []

Num Polynomial where
    (+) = add
    (*) = multiply
    fromInteger x = let x' = (cast {to=Double} x) in withCoefficients [x']

Neg Polynomial where
    (-) = subtract
    negate = mapP negate
    abs = mapP abs


roots : (Num t, Fractional t) => (f : Polynomial) -> Vect n t

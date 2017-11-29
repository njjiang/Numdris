-- ------------------------------------------------------------- [ Polynomial.idr ]
-- Module      : NumIdris.Polynomial
-- Description : Definitions for polynomials
--
--------------------------------------------------------------------- [ EOH ]


module NumIdris.Polynomial

import Data.Vect

%access public export

polynomial : (Num t) => (deg : Nat) -> (coeff : Vect (S deg) t) -> t -> t
polynomial deg coeff x = let xpow = map (pow x) (natRange (S deg)) in
                         foldl1 (+) (zipWith (*) (toList coeff) xpow)


-- needs refactoring

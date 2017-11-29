-- ------------------------------------------------------------- [ Polynomial.idr ]
-- Module      : NumIdris.Polynomial
-- Description : Definitions for polynomials
--
--------------------------------------------------------------------- [ EOH ]


data Polynomial : (Num t) => (deg : Nat) -> (coeff : Vect deg t)

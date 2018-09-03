module Test.PolynomialTest
import Specdris.Spec

import Data.Vect
import Numdris.Polynomial

%access export
%default total

p0 : Polynomial
p0 = WithCoefficients [1.0,1.2, 0.0, 1.0]
-- (1+1.2x+x^3)

p0' : Polynomial
p0' = WithCoefficients [1.2, 0.0, 3.0]
-- (1.2+3x^2)

p0i : Polynomial
p0i = WithCoefficients [0, 1, 0.6, 0, 0.25]
-- (x+0.6x^2+0.25x^4)

p00 : Polynomial
p00 = WithCoefficients [1,1.2, 0, 1, 0, 0, 0, 0]

p3 : Polynomial
p3 = WithCoefficients [3,3,3]
-- (3+3x+3x^2)

foo : Polynomial
foo = WithCoefficients [2,-5,8]
-- (2-5x+8x^2)

foo' :Polynomial
foo' = WithCoefficients [-5,16]
-- (-5+16x)

fooi : Polynomial
fooi = WithCoefficients [0,2,(-5)/2, 8/3]


foo1 : Polynomial
foo1 = WithCoefficients [4,0,0,33,-6]
-- (4+33x^3-6x^4)

partial
polyTest : SpecTree
polyTest = describe "polynomial test" $ do
           it "Evaluate a polynomial" $ do
              eval p0 2 `shouldBe` 11.4
           it "Trim a polynomial" $ do
              trim p00 `shouldBe` p0
           it "Polynomials algebra" $ do
              p3 + p0 `shouldBe` WithCoefficients [4.0, 4.2, 3.0, 1.0]
              p3 - p0 `shouldBe` WithCoefficients [2.0, 1.8, 3.0, -1.0]
              abs (negate p3) `shouldBe` p3
              degree p00 `shouldBe` 3
           it "Multiplication" $ do
              foo * foo1 `shouldBe` WithCoefficients [8,-20,32,66,-177,294,-48]
              -- -48 x^6 + 294 x^5 - 177 x^4 + 66 x^3 + 32 x^2 - 20 x + 8
              p0 * p3 `shouldBe` WithCoefficients [3,6.6,6.6,6.6,3,3]
              -- 3 x^5 + 3 x^4 + 6.6 x^3 + 6.6 x^2 + 6.6 x + 3
           it "differentiate" $ do
              (differentiate p0) `shouldBe` p0'
              (differentiate foo) `shouldBe` foo'
           it "integrate" $ do
              (integrate p0) `shouldBe` p0i
              (integrate foo) `shouldBe` fooi



partial
specSuite : IO ()
specSuite = spec $ do
            polyTest

module Test.PolynomialTest
import Specdris.Spec

import Data.Vect
import Numdris.Polynomial

%access export
%default total

p0 : Polynomial
p0 = withCoefficients [1.0,1.2, 0.0, 1.0]


p00 : Polynomial
p00 = withCoefficients [1.0,1.2, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0]

p3 : Polynomial
p3 = withCoefficients [3.0,3.0,3.0]


partial
polyTest : SpecTree
polyTest = describe "polynomial test" $ do
           it "evaluate a polynomial" $ do
              eval p0 2 `shouldBe` 11.4
           it "trim a polynomial" $ do
              trim p00 `shouldBe` p0
           it "polynomials algebra" $ do
              p3 + p0 `shouldBe` withCoefficients [4.0, 4.2, 3.0, 1.0]
              p3 - p0 `shouldBe` withCoefficients [2.0, 1.8, 3.0, -1.0]
              abs (negate p3) `shouldBe` p3
              degree p00 `shouldBe` 3




partial
specSuite : IO ()
specSuite = spec $ do
            polyTest

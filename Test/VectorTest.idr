module Test.VectorTest
import Specdris.Spec

import Data.Vect as Vect
import Numdris.Vect.Util
import Numdris.Field


%access export
%default total

partial
v1 : List Integer
v1 = toList $ snd (arange 1 5 2)

v2 : Vect 4 Double
v2 = fromList [3.2, 4.1, 99.9, 6]

v3 : Vect 3 Integer
v3 = fromList [1,3,5]

partial
basicSpec : SpecTree
basicSpec = describe "Test basic vector manipulations" $ do
            it "Construct vectors" $ do
               initVector 10 4.2 `shouldBe` replicate 10 4.2
               zeros 6 `shouldBe` replicate 6 0
               ones 8 `shouldBe` replicate 8 1
               v1 `shouldBe` [1,3]
            it "scale a vector" $ do
               scale 6 (ones 10) `shouldBe` replicate 10 6
            it "max/min" $ do
               max v2 `shouldBe` 99.9
               finToNat (argmax v2) `shouldBe` 2
               min v2 `shouldBe` 3.2
               finToNat (argmin v2) `shouldBe` 0
            it "algebra" $ do
               add v3 v3 `shouldBe` (fromList [2,6,10])
               dot v3 v3 `shouldBe` 35
               transpose v3 `shouldBe` (fromList [[1],[3],[5]])




partial
specSuite : IO ()
specSuite = spec $ do
            basicSpec

module Test.GaussianEliminationTest
import Specdris.Spec

import Data.Vect as Vect
import Data.Complex
import Numdris.Matrix
import Numdris.Matrix.Algebra
import Numdris.Matrix.GaussianElimination
import Numdris.Field
import Numdris.Vector

%access export
%default partial

testm : Matrix 3 4 Double
testm = splitVect 3 4 (cast {to=Vect (3*4) Double} (natRangeVect 12))

foo2 : Matrix 3 4 Double
foo2 = fst $ eliminateAllColumns testm

elimfoo2 : Matrix 3 4 Double
elimfoo2 = [[4.0, 5.0, 6.0, 7.0], [0.0, 1.0, 2.0, 3.0], [0.0, 0.0, 0.0, 0.0]]

foo : Matrix 3 4 Double
foo = fromList $ [[4.0, 5.0, 6.0, 7.0], [0.0, 1.0, 2.0, 3.0], [8.0, 9.0, 10.0, 11.0]]


foo1 : Matrix 1 1 Double
foo1 = [[1]]

elimfoo1 : Matrix 1 1 Double
elimfoo1 = fst $ eliminateAllColumns foo1

bar1 : Matrix 3 3 Double
bar1 = [[1,1,3], [4,5,6],[7,8,9]]

elimbar1 : Matrix 3 3 Double
elimbar1 = [[1,1,3], [0,1,-6],[0,0,-6]]


lowerbar1' : Maybe (Matrix 3 3 Double)
lowerbar1' = findLower bar1

lowerbar1 : Matrix 3 3 Double
lowerbar1 = [[1,0,0], [4,1,0],[7,1,1]]

singularm : Matrix 3 3 Double
singularm = [[0,1,2], [3,4,5],[6,7,8]]

elimSpec : SpecTree
elimSpec = describe "elimination" $ do
           it "eliminates" $ do
              foo1 `shouldBe` elimfoo1
              foo2 `shouldBe` elimfoo2
              (fst $ eliminateAllColumns bar1) `shouldBe` elimbar1
              (fst $ eliminateAllColumns [[]]) `shouldBe` [[]]
           it "LU Decomposition" $ do
              (findLower bar1) `shouldBe` (Just lowerbar1)
              (findLower singularm) `shouldBe` Nothing


specSuite : IO ()
specSuite = spec $ do
            elimSpec

module Test.MatrixTest
import Specdris.Spec

import Data.Vect as Vect
import Data.Complex
import Numdris.Matrix
import Numdris.Field

%access export
%default total


m1 : Matrix 2 2 Integer
m1 = Vect.fromList [[1,2]
                   ,[3,4]]


m2 : Matrix 2 2 Integer
m2 = Vect.fromList [[3,4]
                   ,[5,6]]

mdet : Matrix 3 3 Integer
mdet = Vect.fromList [[7,2,9] ,[5,6,3], [3,2,4]]

basis6 : Vect 6 (Vect 2 (Vect 3 Integer))
basis6 = Vect.fromList([[[1, 0, 0], [0, 0, 0]],
[[0, 1, 0], [0, 0, 0]],
[[0, 0, 1], [0, 0, 0]],
[[0, 0, 0], [1, 0, 0]],
[[0, 0, 0], [0, 1, 0]],
[[0, 0, 0], [0, 0, 1]]])


basicSpec : SpecTree
basicSpec = describe "Test some basic manipulations" $ do
            it "take the first row" $ do
               getRow FZ m1 `shouldBe` (Vect.fromList [1,2])
            it "take the second column" $ do
               getColumn (FS FZ) m2 `shouldBe` (Vect.fromList [4, 6])
            it "take an entry" $ do
               entry (FZ, (FS FZ)) m2 `shouldBe` 4
            it "delete a row" $ do
               deleteRowAt FZ m1 `shouldBe` (Vect.fromList [[3,4]])
            it "delete a column" $ do
               deleteColumnAt FZ m1 `shouldBe` (Vect.fromList [[2],[4]])
            it "insert a row" $ do
               insertRowAt (FS FZ) (fromList [0,0]) m1 `shouldBe` (Vect.fromList [[1,2],[0,0],[3,4]])
            it "insert a column" $ do
               insertColumnAt (FS FZ) (fromList [0,0])m1 `shouldBe` (Vect.fromList [[1,0,2], [3,0,4]])
            it "identity matrix" $ do
               identityM 3 `shouldBe` (fromList [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
            it "replace entry" $ do
               replaceEntry (FZ, FZ) 1 (zerosM 2 2) `shouldBe` (Vect.fromList [[1, 0], [0, 0]] )
            it "standard basis" $ do
               basis (zerosM 2 3) `shouldBe` basis6



algebraSpec : SpecTree
algebraSpec = describe "Test matrix algebra" $ do
              it "add two matrices" $ do
                 (add m1 m2) `shouldBe` (Vect.fromList [[4, 6], [8, 10]])
              it "multiply two matrices" $ do
                 (multiply m1 m2) `shouldBe` (Vect.fromList [[13, 16], [29, 36]] )
              it "determinant" $ do
                 determinant mdet `shouldBe` 32


m3 : Matrix 2 2 (Complex Integer)
m3 = iterateM (:+ 2) m1

m4 : Matrix 2 3 Integer
m4 = fill 20 2 3

m4t : Matrix 3 2 Integer
m4t = fill 20 3 2

m4c : Matrix 2 3 (Complex Integer)
m4c = iterateM (:+ 1) m4

m4cconjtrans : Matrix 3 2 (Complex Integer)
m4cconjtrans = iterateM (:+ -1) m4t



complexSpec : SpecTree
complexSpec = describe "Test complex fields operations" $ do
              it "take real part" $ do
                 real m3 `shouldBe` m1
              it "take imag part" $ do
                 imaginary m3 `shouldBe` (fill 2 2 2)
              it "take conjugate" $ do
                 conjugate m4c `shouldBe` (iterateM (:+ -1) m4)
              it "take conjugate transpose" $ do
                 conjugateTranspose m4c `shouldBe` m4cconjtrans


specSuite : IO ()
specSuite = spec $ do
            basicSpec
            algebraSpec
            complexSpec

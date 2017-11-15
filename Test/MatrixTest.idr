module Test.MatrixTest
import Specdris.Spec

import Data.Vect as Vect
import NumIdris.Matrix
import NumIdris.Field

%access export
%default total


m1 : Matrix 2 2 Integer
m1 = Vect.fromList [[1,2]
                   ,[3,4]]


m2 : Matrix 2 2 Integer
m2 = Vect.fromList [[3,4]
                   ,[5,6]]


basicSpec : SpecTree
basicSpec = describe "Test some basic manipulations" $ do
            it "take the first row" $ do
               row FZ m1 `shouldBe` (Vect.fromList [1,2])
            it "take the second column" $ do
               column (FS FZ) m2 `shouldBe` (Vect.fromList [4, 6])
            it "take an entry" $ do
               entry FZ (FS FZ) m2 `shouldBe` 4
            it "delete a row" $ do
               deleteRowAt FZ m1 `shouldBe` (Vect.fromList [[3,4]])
            it "delete a column" $ do
               deleteColumnAt FZ m1 `shouldBe` (Vect.fromList [[2],[4]])
            it "insert a row" $ do
               insertRowAt (FS FZ) (fromList [0,0]) m1 `shouldBe` (Vect.fromList [[1,2],[0,0],[3,4]])
            it "insert a column" $ do
               insertColumnAt (FS FZ) (fromList [0,0])m1 `shouldBe` (Vect.fromList [[1,0,2], [3,0,4]])


algebraSpec : SpecTree
algebraSpec = describe "Test matrix algebra" $ do
              it "add two matrices" $ do
                 (add m1 m2) `shouldBe` (Vect.fromList [[4, 6], [8, 10]])
              it "multiply two matrices" $ do
                 (multiply m1 m2) `shouldBe` (Vect.fromList [[13, 16], [29, 36]] )


specSuite : IO ()
specSuite = spec $ do
            basicSpec
            algebraSpec

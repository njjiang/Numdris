module Test.SparseMatrixTest
import Specdris.Spec

import Data.Vect
import Data.SortedMap
import Numdris.Field
import Numdris.SparseMatrix


%access export
%default total


emptysparse : SparseMatrix 3 3 Integer
emptysparse = MkSparseMatrix $ fromList []

-- [[0, 2,0],[3,0,0],[0,0,0]]
foo : SparseMatrix 3 3 Integer
foo = MkSparseMatrix $ fromList [((FS FZ, FZ), 3), ((FZ, FS FZ), 2)]

-- [[1, 42,0],[0,0,0],[0,0,0]]
foo1 : SparseMatrix 3 3 Integer
foo1 = MkSparseMatrix $ fromList [((FZ, FZ), 1), ((FZ, FS FZ), 42)]

fooadd : SparseMatrix 3 3 Integer
fooadd = MkSparseMatrix $ fromList [((FZ, FZ), 1), ((FS FZ, FZ), 3), ((FZ, FS FZ), 44)]


-- [[0, 0, 0, 0, 0], [0, 0, 90, 0, 0], [42, 0, 0, 0, 0], [0, 0, 0, 0, 0]]
bar : SparseMatrix 4 5 Integer
bar = MkSparseMatrix $ fromList [((FS (FS FZ), FZ), 42), ((FS FZ, FS (FS FZ)), 90)]

-- [[0, 0, 0], [0, 0, 8], [0, 7, 0], [0, 0, 0], [0, 0, 0]]
bar1 : SparseMatrix 5 3 Integer
bar1 = MkSparseMatrix $ fromList [((FS (FS FZ), FS FZ), 7), ((FS FZ, FS (FS FZ)), 8)]

partial
sparseTest : SpecTree
sparseTest = describe "Test sparse matrices" $ do
             it "add two matrices" $ do
                add foo foo1 `shouldBe` fooadd
             it "multiply two matrices" $ do
                toMatrix (multiply foo foo1) `shouldBe` [[0, 0, 0], [3, 126, 0], [0, 0, 0]]
                toMatrix (multiply bar bar1) `shouldBe` [[0, 0, 0], [0, 630, 0], [0, 0, 0], [0, 0, 0]]
             it "convert to matrix" $ do
                toMatrix foo `shouldBe` [[0, 2,0],[3,0,0],[0,0,0]]
                toMatrix (replaceEntry (FZ, FS FZ) 0 foo) `shouldBe` [[0, 0, 0], [3, 0, 0], [0, 0, 0]]
partial

specSuite : IO ()
specSuite = spec $ do
            sparseTest

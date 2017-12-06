module Test.NDVectTest
import Specdris.Spec

import Data.Vect as Vect
import Numdris.Matrix
import Numdris.Field
import Numdris.NDVect

%access export
%default total


foo : NDVect 0 [] Integer
foo = 42



-- sol : NDVect 6 [3,3,3,2,2,3] Integer
-- sol = [[[[[[ 0,  0,  0],
--            [ 0,  0,  0]],
--           [[ 0,  0,  0],
--            [ 0,  0,  0]]],
--          [[[ 1,  2,  3],
--            [ 1,  2,  3]],
--           [[ 1,  2,  3],
--            [ 1,  2,  3]]],
--          [[[ 2,  4,  6],
--            [ 2,  4,  6]],
--           [[ 2,  4,  6],
--            [ 2,  4,  6]]]],
--         [[[[ 3,  6,  9],
--            [ 3,  6,  9]],
--           [[ 3,  6,  9],
--            [ 3,  6,  9]]],
--          [[[ 4,  8, 12],
--            [ 4,  8, 12]],
--           [[ 4,  8, 12],
--            [ 4,  8, 12]]],
--          [[[ 5, 10, 15],
--            [ 5, 10, 15]],
--           [[ 5, 10, 15],
--            [ 5, 10, 15]]]],
--         [[[[ 6, 12, 18],
--            [ 6, 12, 18]],
--           [[ 6, 12, 18],
--            [ 6, 12, 18]]],
--          [[[ 7, 14, 21],
--            [ 7, 14, 21]],
--           [[ 7, 14, 21],
--            [ 7, 14, 21]]],
--          [[[ 8, 16, 24],
--            [ 8, 16, 24]],
--           [[ 8, 16, 24],
--            [ 8, 16, 24]]]]],
--        [[[[[ 9, 18, 27],
--            [ 9, 18, 27]],
--           [[ 9, 18, 27],
--            [ 9, 18, 27]]],
--          [[[10, 20, 30],
--            [10, 20, 30]],
--           [[10, 20, 30],
--            [10, 20, 30]]],
--          [[[11, 22, 33],
--            [11, 22, 33]],
--           [[11, 22, 33],
--            [11, 22, 33]]]],
--            [[[[12, 24, 36],
--            [12, 24, 36]],
--           [[12, 24, 36],
--            [12, 24, 36]]],
--          [[[13, 26, 39],
--            [13, 26, 39]],
--           [[13, 26, 39],
--            [13, 26, 39]]],
--          [[[14, 28, 42],
--            [14, 28, 42]],
--           [[14, 28, 42],
--            [14, 28, 42]]]],
--         [[[[15, 30, 45],
--            [15, 30, 45]],
--           [[15, 30, 45],
--            [15, 30, 45]]],
--          [[[16, 32, 48],
--            [16, 32, 48]],
--           [[16, 32, 48],
--            [16, 32, 48]]],
--          [[[17, 34, 51],
--            [17, 34, 51]],
--           [[17, 34, 51],
--            [17, 34, 51]]]]],
--        [[[[[18, 36, 54],
--            [18, 36, 54]],
--           [[18, 36, 54],
--            [18, 36, 54]]],
--          [[[19, 38, 57],
--            [19, 38, 57]],
--           [[19, 38, 57],
--            [19, 38, 57]]],
--          [[[20, 40, 60],
--            [20, 40, 60]],
--           [[20, 40, 60],
--            [20, 40, 60]]]],
--         [[[[21, 42, 63],
--            [21, 42, 63]],
--           [[21, 42, 63],
--            [21, 42, 63]]],
--          [[[22, 44, 66],
--            [22, 44, 66]],
--           [[22, 44, 66],
--            [22, 44, 66]]],
--          [[[23, 46, 69],
--            [23, 46, 69]],
--           [[23, 46, 69],
--            [23, 46, 69]]]],
--         [[[[24, 48, 72],
--            [24, 48, 72]],
--           [[24, 48, 72],
--            [24, 48, 72]]],
--          [[[25, 50, 75],
--            [25, 50, 75]],
--           [[25, 50, 75],
--            [25, 50, 75]]],
--          [[[26, 52, 78],
--            [26, 52, 78]],
--           [[26, 52, 78],
--            [26, 52, 78]]]]]]

c : NDVect 1 [2] Integer
c = [1,2]

csol : NDVect 2 [2,2] Integer
csol = [[1,2], [2,4]]

a : NDVect 3 [3,3,3] Integer
a = [[[ 0,  1,  2],
[ 3,  4,  5],
[ 6,  7,  8]],
[[ 9, 10, 11],
[12, 13, 14],
[15, 16, 17]],
[[18, 19, 20],
[21, 22, 23],
[24, 25, 26]]]

b : NDVect 3 [2,2,3] Integer
b = [[[1,2,3],[1,2,3]],
[[1,2,3],[1,2,3]]]


b3 : NDVect 4 [3,2,2,3] Integer
b3 = [
      [[[1,2,3],[1,2,3]],
       [[1,2,3],[1,2,3]]],
      [[[1,2,3],[1,2,3]],
       [[1,2,3],[1,2,3]]],
      [[[1,2,3],[1,2,3]],
       [[1,2,3],[1,2,3]]]]

productSpec : SpecTree
productSpec = describe "test tensor outer product" $ do
                 it "take the tensor product" $ do
                    -- dot a b `shouldBe` sol
                     c <><> c `shouldBe` csol
                 it "entry" $ do
                    entry a [0,1,2] `shouldBe` Just 5
                 it "expand" $ do
                    expand  3 b `shouldBe ` b3

specSuite : IO ()
specSuite = spec $ do
            productSpec

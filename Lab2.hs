module Lab2 where

import Data.List
import Data.Char
import System.Random
import Test.QuickCheck

infix 1 --> 

(-->) :: Bool -> Bool -> Bool
p --> q = not p || q

probs :: Int -> IO [Float]
probs 0 = return []
probs n = do
             p <- getStdRandom random
             ps <- probs (n-1) 
             return (p:ps)
     
-- 1. Check whether randomly generated list of floating point number 
--    is really random. Count the numbers in the quartiles 
--    (0-0,25), (0,25-0,5), (0,5-0,75), (0,75-1).
--  The distribution should be equal.
--  E.g., if you generate 10000 numbers, 
--  then roughly 2500 of them should be in each quartile.

-- Time spent: 2 hours. Most of this time was spent finding out
-- how to work with monads, in combination with 'normal' functions.

-- Result: 
-- Run 1: [1.000416,1.002656,0.999956,0.996972]
-- Run 2: [1.00208,1.001028,0.9976,0.999292]
-- Run 3: [1.000756,1.000112,0.999256,0.999876]
-- The distribution is roughly equal. The difference is no more than 2% in one group.
testProbs :: IO[Float]
testProbs = percentages (quartiles 1000000)

quartiles :: Int -> IO [Int]
quartiles n = do
                  numbers <- probs n
                  let a = length (filter (<0.25) numbers)
                  let b = length (filter (\ n ->  (n > 0.25) && (n < 0.5)) numbers)
                  let c = length (filter (\ n ->  (n > 0.5) && (n < 0.75)) numbers)
                  let d = length (filter (>0.75) numbers)
                  return [a,b,c,d]

percentages :: IO [Int] -> IO [Float]
percentages (xs) = do
                      quarts <- xs
                      let n = (fromIntegral $ sum quarts) / (fromIntegral $ length quarts)
                      let p = map (\q -> (fromIntegral q) / ( n )) (quarts)
                      return p
                        
-- 2. 
-- Time spent 1h
data Shape = NoTriangle | Equilateral 
           | Isosceles  | Rectangular | Other deriving (Eq,Show)
           
triangle :: Integer -> Integer -> Integer -> Shape             
triangle a b c | not ((a+b>c) && (a+c>b) && (b+c>a)) = NoTriangle
               | a==b && b==c         = Equilateral
               | a^2 + b^2 == c^2     = Rectangular
               | a^2 + c^2 == b^2     = Rectangular
               | b^2 + c^2 == a^2     = Rectangular
               | a==b || b==c || a==c = Isosceles
               | otherwise              = Other
               
-- Result: True
testTriangleEq :: Bool
testTriangleEq = triangle 2 2 2 == Equilateral
-- Result: True
testTriangleRec :: Bool
testTriangleRec = all (==Rectangular) [triangle a b c | a <- [3,4,5], b <- [3,4,5], c <- [3,4,5], (a/=b) && (b/=c) && (c/=a)]
               

-- 3. Recognizing Permutations
-- Time Spent: 2:00
-- If duplicates are allowed in the list, isPermutation has to count the number
-- of occurences of an element. It cannot just check the existence of an element
-- in list A in list B. In the implementation below this is done by 'delete' which 
-- will only delete one occurence of the element in the list.
isPermutation :: Eq a => [a] -> [a] -> Bool
isPermutation [] [] = True
isPermutation [] (_:_) = False
isPermutation (x:xs) ys   | (length (x:xs)) /= (length ys) = False
                          | x `notElem` ys                 = False
                          | otherwise                      = isPermutation xs $ delete x ys
                   
-- Properties:
-- All elements in list A also have to be in list B, and viceversa. 
-- Result: True
testIsPerm1 :: Bool
testIsPerm1 = not (isPermutation [1,2] [2,3]) && not (isPermutation [2,3] [1,2])

-- Result: True
testIsPerm2 :: Bool
testIsPerm2 = not (isPermutation [1,2,2] [1,2]) && not (isPermutation [1,2] [1,2,2])       
 
-- Result: True
testIsPerm3 :: Bool
testIsPerm3 = all (==True) [(isPermutation [1] [1]),
                            (isPermutation [1,2] [2,1]),
                            (isPermutation [1,2,2] [2,1,2])]
                
 
 
-- 4. Recognizing and generating derangements 
--    Give a Haskell implementation of a property isDerangement that 
--    checks whether one list is a derangement of another one.        
-- Time Spent: 1:00       
isDerangement :: Eq a => [a] -> [a] -> Bool
isDerangement [] [] = True
isDerangement xs ys | not $ isPermutation xs ys   = False
                    | True `elem` zippedList      = False
                    | otherwise                   = True
                    where zippedList = zipWith (==) xs ys 
                    
-- To optimize performance, the statement:
--  'True `elem` zippedList' 
-- can be replaced with:  
--  'foldr (||) False zippedList' 
                    
-- Give a Haskell implementation of a function deran that 
-- generates a list of all derangements of the list [0..n-1].
-- Time Spent 0:30
deran :: Integer -> [[Integer]] 
deran n = deran' [0..(n-1)]

deran' :: Eq a => [a] -> [[a]]
deran' [] = [[]]
deran' xs = filter (isDerangement xs) (permutations xs)

-- Next, define some testable properties for the isDerangement function, 
-- and use some well-chosen integer lists to test isDerangement.

-- Prop A: List content is not the same (property of isPermutation)
-- Result: True
testIsDeran2 :: Bool
testIsDeran2 = not (isDerangement [1,2] [2,3])

-- Prop B: If there is an element A[x] == B[x] -> false
-- Result: True
testIsDeran1 :: Bool
testIsDeran1 = not (isDerangement [1,2,3] [1,3,2])

-- Prop B: If there is an element A[x] == B[x] -> false
deran_prop :: Eq a => [a] -> [a] -> Bool
deran_prop xs ys = True `notElem` zipWith (==) xs ys

-- Test for Prop B:
-- Time Spent: 2:00
-- If isDerangement is true, the deran_prop should hold.
-- Result: True
testDeranProp :: Bool
testDeranProp = hoareTest (isDerangement [1..6]) id (deran_prop [1..6]) (permutations [1..6])

hoareTest :: (a -> Bool) -> (a -> a) -> (a -> Bool) -> [a] -> Bool
hoareTest precondition f postcondition =
    all (\x -> precondition x --> postcondition (f x))

hoareTestR ::  Fractional t =>
               (a -> Bool)
               -> (a -> a) -> (a -> Bool) -> [a] -> (Bool,t)
hoareTestR precond f postcond testcases = let
       a = fromIntegral (length $ filter precond testcases)
       b = fromIntegral (length testcases)
     in 
       (all (\x ->
         precond x --> postcond (f x)) testcases,a/b)
                  
-- 5. Implementing and testing ROT13 encoding
--  ROT13 is a single letter substitution cipher 
--  that is used in online forums for hiding spoilers.
-- Time Spent: 2:00
upper_alphabet :: String
upper_alphabet = cycle ['A'..'Z']

lower_alphabet :: String
lower_alphabet = cycle ['a'..'z']

-- First, give a specification of ROT13.
--    1. Replace every letter in a String with the letter 13 letters after it.
--    Where: A -> N, N -> A
--           a -> n, n -> a
--    2. Non letter characters will not be changed by the ROT13 algorithm
--    3. Because there are 26 letters in the alphabet, the inverse of a ROT13 
--       encoded String should be the original input.

-- Next, give a simple implementation of ROT13.
rot13 :: String -> String
rot13 = map rot13rotate

rot13rotate :: Char -> Char
rot13rotate c | isUpper c = upper_alphabet!!(head (elemIndices c upper_alphabet) + 13)
              | isLower c = lower_alphabet!!(head (elemIndices c lower_alphabet) + 13)
              | otherwise = c

-- Finally, turn the specification into a series of QuickCheck 
-- properties, and use these to test your implementation.
-- All these tests pass
testRot13_upper, testRot13_lower, testRot13_other, testRot13_inverse :: IO Result
testRot13_upper = quickCheckResult (\n -> (n>=0) --> rot13 upper_alphabet!!n == upper_alphabet!!(n+13))
testRot13_lower = quickCheckResult (\n -> (n>=0) --> rot13 lower_alphabet!!n == lower_alphabet!!(n+13))
testRot13_other = quickCheckResult (\n -> (n>=0 && not (isLetter (chr n))) --> rot13 [chr n] == [chr n])
testRot13_inverse =  quickCheckResult (\n -> (n>=0) --> [ chr c | c <- [0..n] ] == rot13 ( rot13 [ chr c | c <- [0..n]] ))


                            
                            
           
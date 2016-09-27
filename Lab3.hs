module Lab3 where

import Data.List
import System.Random
import Test.QuickCheck
import Lecture3

{-| 1.

  The lecture notes of this week discuss the notions 
  of satisfiability, tautology, contradiction, logical 
  entailment and logical equivalence for formulas of 
  propositional logic.
  
  Time Spent: 2:00
-}

-- Contradiction: There is no valuation that makes f true
contradiction :: Form -> Bool
contradiction = not.satisfiable

-- + = OR = disjunction
-- * = AND = conjunction
-- - = NOT = negation

-- Result: True
isContr = contradiction $ head (parse "*(1 -1)")

tautology :: Form -> Bool
tautology f = all (\ v -> evl v f) (allVals f)

-- Result: True
isTaut = tautology $ head (parse "+(1 -1)")

-- | logical entailment 
-- F1: All A are B
-- F2: All C are A
-- Therefore, all C are B ->  F2 entails F1
-- All valuations that make F2 true, also make F1 true.
-- BELOW ARE TWO VERSIONS:
-- Version A: The hard way, checking whether the True valuations of Form A also are True valuations of Form B.
-- Version B: The easy way, checking whether Form A implies Form B, using the Impl token to create a new Form.

-- Version A: (hard)
entails :: Form -> Form -> Bool
entails a b | length entailedVals == 0 = False
            | otherwise = all (\ v -> evl v b) entailedVals
             where trueValsA = trueVals a
                   trueValsB = trueVals b
                   entailedVals = filterEntails' trueValsA trueValsB
                   
filterEntails :: Valuation -> [Valuation] -> [Valuation]
filterEntails a = filter (\n -> a `isSubsequenceOf` n)

-- Test for filterEntails
testFilterEntails_a = [(1,True)]
testFilterEntails_b = [[(1,True),  (2,True) ], 
                       [(1,True),  (2,False)],
                       [(1,False), (2,True) ],
                       [(1,False), (2,False)]]
testFilterEntails_expected = [[(1,True),  (2,True) ], 
                              [(1,True),  (2,False)]]
                              
-- Result: True
testFilterEntails = filterEntails testFilterEntails_a testFilterEntails_b == testFilterEntails_expected

filterEntails' ::[Valuation] -> [Valuation] -> [Valuation]
filterEntails' [] _ = []
filterEntails' _ [] = []
filterEntails' (x:xs) ys = nub ((filterEntails x ys) ++ (filterEntails' xs ys))

prop1_a = head (parse "1")
prop1_b = head (parse "+(1 2)")

-- Result: True
testEntails1 = entails prop1_a prop1_b
-- Result: True
testEntails2 = entails prop1_a prop1_a
-- Result: True
testEntails3 = entails prop1_b prop1_b
-- Result: True
testEntails4 = not $ entails prop1_b prop1_a

-- Version B: (easy)
entails' :: Form -> Form -> Bool
entails' f1 f2 = tautology $ Impl f1 f2


-- Result: True
testEntails1' = entails' prop1_a prop1_b
-- Result: True
testEntails2' = entails' prop1_a prop1_a
-- Result: True
testEntails3' = entails' prop1_b prop1_b
-- Result: True
testEntails4' = not $ entails' prop1_b prop1_a



trueVals :: Form -> [Valuation]
trueVals f = filter (\ v -> evl v f) (allVals f)

 -- | logical equivalence
equiv :: Form -> Form -> Bool
equiv f1 f2 = tautology $ Equiv f1 f2
 
 
-- Deliverables: 
--   D1.1: Implementation
--   D1.2: Description of your method of checking the definitions,
--   D1.3: Indication of time spent: 3:00

{-| 2. 
  The lecture notes of this week define a function parse 
  for parsing propositional formulas. Test this function. 
  You can use any test method you want.
-}
-- Deliverables:
--   D2.1: Test report describing the test method used and the outcome of the test, 
--   D2.2: Indication of time spent: 2:00
                    
prop_parse :: (Form, String) -> Bool
prop_parse (f,s) | f /= (parsef s)        = False
                 | s /= show f            = False
                 | f /= (parsef $ show f) = False
                 | otherwise              = True
   
formExamples :: [(Form, String)]
formExamples = [(Prop 1,                         "1"),
                (Neg (Prop 1),                   "-1"),
                (Dsj [(Prop 1), (Prop 2)],       "+(1 2)"),
                (Cnj [(Prop 1), (Prop 2)],       "*(1 2)"),
                (Cnj [(Prop 1), (Neg (Prop 2))], "*(1 -2)"),
                (Cnj [(Neg (Prop 1)), (Prop 2)], "*(-1 2)"),
                (Cnj [(Neg (Prop 1)), (Neg (Prop 2))], "*(-1 -2)"),
                (Impl (Prop 1) (Prop 2),         "(1==>2)"),
                (Neg (Impl (Prop 1) (Prop 2)),   "-(1==>2)"),
                (Equiv (Prop 1) (Prop 2),        "(1<=>2)")]
                
-- Result: True
testParse1 = all prop_parse formExamples


-- Using the generator, and only testing whether (parse $ show f) == f
prop_parse_inverse = forAll genForm (\f -> f == (head $ parse $ show f))
-- Command: 
--   verboseCheck $ prop_parse_inverse
-- Result: 
--   +++ OK, passed 100 tests.

parsef :: String -> Form
parsef = head.parse

{-| 3. 
 The lecture notes of this week discuss the conversion of Boolean formulas 
 (formulas of propositional logic) into CNF form. 
 The lecture notes also give a definition of a Haskell datatype 
 for formulas of propositional logic, using lists for conjunctions and disjunctions. 
 Your task is to write a Haskell program for converting formulas into CNF.

Deliverables: 
  D3.1: Conversion program with documentation, 
  D3.2: Indication of time spent: 1:00
-}

--  Part of cnf using arrowfree and nnf
-- cnf :: Form -> Form
-- cnf = arrowfree # nnf

-- CNF in the form of (..∨..) ∧ ... ∧ (..∨..)
falseVals :: Form -> [Valuation]
falseVals f = filter (\v -> not $ evl v f) (allVals f)

-- Conversion steps:
-- 1. Find all False valuations of formule f (falseVals f)
-- 2. For each valuation, negate the values of the atoms, and put them in a disjunction. (cnf_dsj)
-- 3. Do this for all the valuations, and add them to a list (foldr)
-- 4. The conjunction if this list will be the CNF. 

cnf :: Form -> Form
cnf f = Cnj $ foldr (\p n -> (cnf_dsj p):n) [] (falseVals f)

--  Conversion:  [(Name1, True), (Name2, False)] -> (not Name1 ∨ Name2) == Dsj [not Name1, Name2]
cnf_dsj :: Valuation -> Form
cnf_dsj vs = Dsj $ map (\(x,y) -> if y then Neg (Prop x) else (Prop x)) vs

{-| 4. 
  Write a formula generator for random testing of properties of propositional logic, 
  or teach yourself enough QuickCheck to use random QuickCheck testing of formulas.

  Use your random testing method to test the correctness of the conversion program 
  from the previous exercise. Formulate a number of relevant properties to test, 
  and carry out the tests, either with your own random formula generator or with QuickCheck.

  Deliverables: 
    D4.1: Generator for formulas
    D4.2: Sequence of test properties
    D4.3: Test report
    D4.4: Indication of time spent: 2:00
-}

-- D4.1: Generator for formulas
genForm :: Gen Form
genForm =
     do 
        let p = [Prop 1,Prop 2,Prop 3]
        let np = [Neg x | x <- p]
        let conjs = [Cnj x | x <- filter (\y -> length y > 1) (subsequences (p ++ np))]
        id <- elements p
        neg  <-  elements np
        con <- elements [Cnj x | x <- filter (\y -> length y > 1) (take 10 (subsequences (p ++ np)) ++ [conjs])]
        dis <- elements [Dsj x | x <- filter (\y -> length y > 1) (subsequences (p ++ np))]
        imp <- elements [Impl x y | x <- [id,neg,dis,con],y <- [id,neg,dis,con]]
        eq <- elements [Equiv x y | x <- [id,neg,dis,con],y <- [id,neg,dis,con]]
        ba <- elements [Neg x | x <- [id,neg,dis,con]]
        r <- elements [id,neg,dis,imp,eq,con,ba]
        return r

isNotInfixOf :: Eq a => [a] -> [a] -> Bool
isNotInfixOf xs ys = not $ isInfixOf xs ys

-- D4.2: Sequence of test properties
-- D4.3: Test report

-- Postconditions for arrowfree:
-- 1. Should not contain implication (==>) or double implication (<=>)
no_implication_prop f = forAll genForm (\n -> "=>" `isNotInfixOf` (show(f n)))
-- Command: 
--   verboseCheck $ no_implication_prop id
-- Result: 
--   *** Failed! Falsifiable (after 1 test):
--   (-3==>*(2 3))

-- Command: 
--   verboseCheck $ no_implication_prop arrowfree
-- Result: 
--   +++ OK, passed 100 tests.
--

-- Command: 
--   verboseCheck $ no_implication_prop cnf 
-- Result: 
--   +++ OK, passed 100 tests.

-- For nnf and arrowfree:
-- 2. Input and output should be equivalent
equivalent_prop f = forAll genForm (\n-> equiv n (f n))
-- Command: 
--   verboseCheck $ equivalent_prop id
-- Result: 
--   +++ OK, passed 100 tests.

-- Command: 
--   verboseCheck $ equivalent_prop arrowfree
-- Result: 
--   +++ OK, passed 100 tests.

-- Command: 
--   verboseCheck $ equivalent_prop cnf
-- Result: 
--   +++ OK, passed 100 tests.

-- For nnf:
-- 3. Negation signs are allowed only in front of proposition letters.
only_letter_negation f = all (\n -> n `isNotInfixOf` (show f)) ["-+", "-*"]
only_letter_negation_prop f = forAll genForm (\n -> only_letter_negation (f n))

-- Command: 
--   verboseCheck $ only_letter_negation_prop id
-- Result: 
--   *** Failed! Falsifiable (after 15 tests):
--   -+(1 2 3 -1 -3)

-- Command: 
--   verboseCheck $ only_letter_negation_prop arrowfree
-- Result: 
--   *** Failed! Falsifiable (after 5 tests):
--   -+(-2 -3)

-- Command: 
--   verboseCheck $ only_letter_negation_prop cnf
-- Result: 
--   +++ OK, passed 100 tests.

{-| 5. 

  In SAT solving, one common technique is resolution style theorem proving. 
  For that, it is usual to represent a formula in CNF as a list of clauses, 
  were a clause is a list of literals, and where a literal is represented as an integer, 
  with negative sign indicating negation. 
  
  Clauses should be read disjunctively, and clause lists conjunctively. 
  5 represents the atom p5,
  −5 represents the literal ¬p5, 
  The clause [5,−6] represents p5∨¬p6, 
  The clause list [[4],[5,−6]] represents the formula p4∧(p5∨¬p6).

  Write a program for converting formulas to clause form.

  If you combine your conversion function from an earlier exercise with cnf2cls 
  you have a function that can convert any formula to clause form.

  Use automated testing to check whether your translation is correct, 
  employing some appropriate properties to check.


Deliverables: 
  D5.1: Conversion program
  D5.2: Test generator
  D5.3: Test properties
  D5.4: Documentation of the automated testing process
  D5.5: Indication of time spent: 3:00
-}
type Clause  = [Int]
type Clauses = [Clause]
    
-- p4∧(p5∨¬p6) -> [[4],[5,−6]]
cnf2cls :: Form -> Clauses
cnf2cls (Cnj fs) = map cnf2cls' fs
cnf2cls  _       = error "Formula not in CNF"

-- Test:
--   Command:  cnf2cls (Cnj [(Prop 4), (Dsj [(Prop 5), (Neg (Prop 6))])])
--    Result:  [[4],[5,-6]]

cnf2cls' :: Form -> Clause
cnf2cls' (Neg (Neg f))  = cnf2cls' f
cnf2cls' (Dsj fs)       = foldr (\n p -> cnf2cls' n ++ p) [] fs
cnf2cls' (Prop x)       = [x]
cnf2cls' (Neg (Prop x)) = [-x]
cnf2cls'  _             = error "Formula not in CNF"


-- D5.1: Conversion program
form2cls :: Form -> Clauses 
form2cls = cnf # cnf2cls

-- D5.2: Test generator.  Using the test generator from exercise 4.

-- D5.3: Test properties
-- D5.4: Documentation of the automated testing process

-- Lenght of the clauses list should equal the number of conjuncts.
correct_length_prop :: Property
correct_length_prop = forAll genForm (\n -> numberOfCnjs (cnf n) == length (form2cls n))
                       where numberOfCnjs (Cnj fs) = length fs
                             numberOfCnjs (Prop _) = 1
                             numberOfCnjs (Neg (Prop _)) = 1
                             numberOfCnjs _ = error "Formula not in CNF"
-- Command: 
--   quickCheck correct_length_prop
-- Result:
--   +++ OK, passed 100 tests.



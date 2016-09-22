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
-}

-- Contradiction: There is no valuation that makes f true
contradiction :: Form -> Bool
contradiction = not.satisfiable

-- + = OR = disjunction
-- * = AND = conjunction
-- - = NOT = negation
isContr = contradiction $ head (parse "*(1 -1)")

tautology :: Form -> Bool
tautology f = all (\ v -> evl v f) (allVals f)

isTaut = tautology $ head (parse "+(1 -1)")

-- | logical entailment 
-- F1: All A are B
-- F2: All C are A
-- Therefore, all C are B ->  F2 entails F1
-- All valuations that make F2 true, also make F1 true.
entails :: Form -> Form -> Bool
entails a b | length entailedVals == 0 = False
            | otherwise = all (\ v -> evl v b) entailedVals
             where trueValsA = trueVals a
                   trueValsB = trueVals b
                   entailedVals = filterEntails' trueValsA trueValsB
                   
filterEntails :: Valuation -> [Valuation] -> [Valuation]
filterEntails a = filter (\n -> a `isSubsequenceOf` n)

testFilterEntails_a = [(1,True)]
testFilterEntails_b = [[(1,True),  (2,True) ], 
                       [(1,True),  (2,False)],
                       [(1,False), (2,True) ],
                       [(1,False), (2,False)]]
testFilterEntails_expected = [[(1,True),  (2,True) ], 
                              [(1,True),  (2,False)]]
testFilterEntails = filterEntails testFilterEntails_a testFilterEntails_b == testFilterEntails_expected

filterEntails' ::[Valuation] -> [Valuation] -> [Valuation]
filterEntails' [] _ = []
filterEntails' _ [] = []
filterEntails' (x:xs) ys = nub ((filterEntails x ys) ++ (filterEntails' xs ys))

prop1_a = head (parse "1")
prop1_b = head (parse "+(1 2)")
testEntails1 = entails prop1_a prop1_b
testEntails2 = entails prop1_a prop1_a
testEntails3 = entails prop1_b prop1_b
testEntails4 = not $ entails prop1_b prop1_a

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

prop_unambiguous :: String -> Bool
prop_unambiguous s = length (parse s) == 1

prop_show :: String -> Bool
prop_show s = length forms == 1 --> (show form) == s
              where forms = parse s
                    form = head forms
                    
prop_parse :: (Form, String) -> Bool
prop_parse (f,s) | f /= (parsef s)        = False
                 | s /= show f            = False
                 | f /= (parsef $ show f) = False
                 | otherwise              = True

prop_parse_inverse :: Form -> Bool 
prop_parse_inverse f = f == (head $ parse $ show f)
   
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


cnfExamples :: [(Form, Form)]
cnfExamples = [ 
--              ¬¬¬p  <=>  ¬p
                (Neg (Neg (Neg (Prop 1))), Neg (Prop 1)),
--               ¬(p∨¬q)  <=> (¬p∨¬q) ∧ (¬p∨q) ∧ (p∨q)

                (parsef "-+(1 -2)", parsef "*(+(-1 -2) +(-1 2) +(1 2))"),
--              ¬(¬p∧¬q)  <=> p∨q
                (Neg (Cnj [(Neg (Prop 1)), (Neg (Prop 2))]), Dsj [(Prop 1), (Prop 2)])
                ]

               
cnf :: Form -> Form
cnf = arrowfree # nnf

isNotInfixOf :: Eq a => [a] -> [a] -> Bool
isNotInfixOf xs ys = not $ isInfixOf xs ys

-- Postconditions for cnf:
-- Should not contain implication (==>) or double implication (<=>)
no_implication_prop = forAll genForm (\f -> "=>" `isNotInfixOf` (show(cnf f)))

-- Input and output should be equivalent
cnf_eq_prop = forAll genForm (\f -> equiv f (cnf f))

-- Negation signs are allowed only in front of proposition letters.
only_letter_negation f = all (\n -> n `isNotInfixOf` (show f)) ["-+", "-*"]

-- Command: verboseCheck $ only_letter_negation_prop arrowfree
-- Result: 
-- *** Failed! Falsifiable (after 2 tests):
-- (*(1 2 3)<=>+(1 3 -1 -2))
--
-- Command: verboseCheck $ only_letter_negation_prop cnf
-- Result: 
-- +++ OK, passed 100 tests.
only_letter_negation_prop f = forAll genForm (\n -> only_letter_negation (f n))


testCnf = all (\(x,y) -> equiv x (cnf x)) cnfExamples


{-| 4. 

Formulate a number of relevant properties to test.
-}

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
        r <- elements ([id,neg,dis,imp,eq,con])
        return (r)





            
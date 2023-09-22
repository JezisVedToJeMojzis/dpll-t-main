{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE NegativeLiterals #-}
module CNF.DPLL
  ( Solution
  , resolve
  , ple
  , bcp
  , branch
  , dpll
  , satisfiable
  ) where

import Prelude hiding (negate)

import CNF.Types

import Data.Functor.Identity (runIdentity)
import Data.Maybe (mapMaybe)

import Control.Applicative
import Control.Monad ((>=>), foldM)
import Control.Monad.Writer
import Control.Monad.Trans.Maybe (runMaybeT)


-- | A solution given by the DPLL algorithm.
type Solution a = [Lit a]

-- | A monad m solves over the type a with the following constraints.
type Solver a m = (MonadWriter (Solution a) m, Alternative m, Eq a)

-- | Unit Resolution
--
-- Given a literal and a CNF, remove all occurences of it in the CNF according
-- to Unit Resolution. This implementation can be useful in all three stages
-- of the DPLL algorithm.
--
-- e.g. resolve (Lit p) [[Lit p], [Lit q], [Neg p]] == [[Lit q], []]
--
-- Notice how an occurence of the literal resolves the whole Or while occurence
-- of its negation removes the literal. You may assume that any literal occurs
-- in any given Or at most once.
--
-- Make sure to add the literal that will be resolved to the solution via
-- a call to 'tell'!

-- check cnf
litInCnf :: Eq a => Lit a -> CNF a -> Bool
litInCnf lit cnf = any (elem lit) cnf

negLitInCnf :: Eq a => Lit a -> CNF a -> Bool
negLitInCnf negatedLit cnf = any (elem negatedLit) cnf

--check clauses
litInClause :: Eq a => Lit a -> [Lit a] -> Bool
litInClause lit clause = lit `elem` clause

negLitInClause :: Eq a => Lit a -> [Lit a] -> Bool
negLitInClause negLit clause = negate negLit `elem` clause

mixedCases :: Eq a => Lit a -> [Lit a] -> Bool
mixedCases lit clause = lit `elem` clause && negate lit `elem` clause

--remove empty brackets
removeEmptyClauses :: CNF a -> CNF a
removeEmptyClauses = filter (not . null)

--removing the lit but keeping the clause (brackets [])
filterClauseNeg :: Eq a => Lit a -> [Lit a] -> [Lit a]
filterClauseNeg lit clause
      | negLitInClause lit clause = filter (/= negate lit) clause
      | otherwise = clause 

convertToSingleCNF :: [CNF a] -> CNF a
convertToSingleCNF = concat

-- Tests:
-- removes Or if it contained the literal 
-- removes literal from Or if negation was contained 
-- does both operations when cases are mixed 
-- adds literals to the model when it resolves them 
resolve :: Solver a m => CNF a -> Lit a -> m (CNF a)
resolve cnf lit = do
    let updatedCnfLit = filterClauseLit lit <$> cnf
    let updatedCnfNeg = filterClauseNeg lit <$> convertToSingleCNF updatedCnfLit
    tell [lit] -- logging
    return updatedCnfNeg
  where
    filterClauseLit :: Eq a => Lit a -> [Lit a] -> CNF a --removing the clause if lit was there
    filterClauseLit lit clause
      | litInClause lit clause = []  -- remove the whole clause
      | null clause = [[]] -- keep initial empty brackets
      | otherwise = [clause] -- nothing changes

  
-- | Pure Literal Elimination (PLE)
--
-- Resolve variables if they only occur positively or
-- negatively (but not both), according to Pure Literal
-- Elimination
--
-- Do make sure to remove new pure literals that
-- occur due to PLE!

litsInCnf :: CNF a -> [Lit a]
litsInCnf = foldr (++) []

getNegativeLiterals :: Eq a => CNF a -> [Lit a]
getNegativeLiterals cnf = filter (\lit -> not (litInCnf lit cnf)) (litsInCnf cnf)

getPositiveLiterals :: Eq a => CNF a -> [Lit a]
getPositiveLiterals cnf = filter (\lit -> not (negLitInCnf (negate lit) cnf)) (litsInCnf  cnf)

-- getPureLiterals :: Eq a => CNF a -> [Lit a]
-- getPureLiterals cnf = getPositiveLiterals cnf ++ getNegativeLiterals cnf

getPureLiterals :: Eq a => CNF a -> [Lit a]
getPureLiterals cnf = 
  let
    positiveLiterals = getPositiveLiterals cnf
    negativeLiterals = getNegativeLiterals cnf
    in positiveLiterals ++ negativeLiterals

-- there cant be variable which is positive (not negated) and negated at the same time
-- Tests:
-- resolves occurences of pure literals / works
-- recursively resolves new pure literals / works
ple :: Solver a m => CNF a -> m (CNF a)
ple cnf = do
    let pureLiterals = getPureLiterals cnf
    if not (null pureLiterals) 
        then do
            tell pureLiterals
            let updatedCnf =  [clause | clause <- cnf, not (any (`elem` pureLiterals) clause)] -- filters caluses that contain pureLiterals
            ple updatedCnf  -- recursion
        else 
          return cnf

-- | Boolean Constraint Propagation (BCP)
--
-- Remove all occurences of single variables according
-- to Boolean Constraint Propagation.
--
-- Do make sure to remove new single occurences that
-- occur due to BCP!
bcp :: Solver a m => CNF a -> m (CNF a)
bcp = undefined 


-- | Attempts to solve the constraints by resolving
-- the given literal. Picking a constraint in this
-- way may fail the recursive dpll call, which is
-- why this function is call 'try'.
--
-- You may want to implement this function as a
-- helper for 'branch'.
try :: Solver a m => CNF a -> Lit a -> m () --idk if it really works since resolve is not rly correct
try cnf lit = do
    resolvedCnf <- resolve cnf lit
    dpll resolvedCnf -- recursion

-- | Branch in the Depth First Search. (i.e. try both occurences of a variable)
--
-- Three cases may happen here:
-- - There is no more solution for this branch (i.e. empty disjunct [] exists).
--   Signify failure via 'empty'
--
-- - There is a variable to choose. 
--   'try' both a positive and negative occurence.
--   Hint: Use (<|>)
--
-- - There is *no* more variable to choose.
--   This branchs offers a solution! Signify succes via 'return ()'
--
-- Return type: You may return `pure ()` when it is satifiable and `empty`
-- otherwise. This will also allow you to compose branches via the (<|>)
-- operator. More precisely, for two functions f1 and f2, f1 <|> f2 will first
-- try if f1 succeeds (in our case, succeeding means proving satisfiability),
-- and if not, try f2. This will be useful when assigning tentative values to
-- Boolean variables.
--
-- We don't expect any heuristics to pick branches in this implementation. Thus,
-- you may just pick any literal to branch on.
branch :: Solver a m => CNF a -> m ()
branch = undefined

-- | The DPLL procedure. 
--
-- Finds whether a given CNF is satisfiable.
--
-- A CNF is satisfiable when all of its conjuncts are resolved. In our case,
-- when we have [] :: CNF a
--
-- A CNF is unsatisfiable when it contains an Or that contains no literals.
-- e.g., [[], ...] is unsat
dpll :: Solver a m => CNF a -> m ()
dpll = ple >=> bcp >=> branch

-- | Check a given CNF for satisfiability. Returning a model
-- when there is one.
satisfiable :: Eq a => CNF a -> Maybe (Solution a)
satisfiable = runIdentity . runMaybeT . execWriterT . dpll

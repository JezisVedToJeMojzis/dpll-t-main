module CNF.Transform
  ( distribute
  , cnf
  ) where

import AST.Prop
import CNF.Types (CNF)
import qualified CNF.Types as CNF

-- | This function implements the distribution 
-- of disjunction over conjunction.
--
-- The function takes as arguments two 
-- propositions p and q, representing formula p | q, 
-- and exhaustively applies the distribution operation.
--
-- An example of a distribution:
--
-- $ distribute (a & b & c) (d & (e | f))
-- > (a | d) & (a | e | f) & (b | d) & (b | e | f) & (c | d) & (c | e | f)
--
-- Note that this solution will be in the rigid CNF format, which
-- means that the actual result will look more like:
--
-- $ distribute [[a], [b], [c]] [[d], [e, f]]
-- > [ [a, d], [a | e | f], [b, d], [b, e, f], [c, d], [c, e, f] ]
--
-- Note: While it is technically correct to order the distribution differently
-- (modulo commutativity), this is a nightmare to check programatticaly. For
-- this reason, we require your implementation to distribute in the order shown
-- above!
--
-- Hint: You may want to define a helper function that distributes a single Or
-- over the entire second argument.
--
-- Though won't grade on it, you can try to implement this function without
-- pattern matching on the lists. Haskell already provides a lot of functions
-- to operate on lists!
-- Helper function to distribute a single clause (OR operation) over CNF

--Helper 
helpDistribute :: [[CNF.Lit a]] -> CNF a -> CNF a -- [[CNF.Lit a]] is list of clauses and each clause is list of literals
helpDistribute [] _ = []
helpDistribute (p : ps) q = [clause ++ p | clause <- q] ++ helpDistribute ps q -- p is being distributed over q

-- Tests:
-- correctly computes the base case (no conjuncts) / works
-- correctly distributes singles /works
-- correctly recursively distributes /works
distribute :: CNF a -> CNF a -> CNF a
distribute [] _ = []
distribute (p : ps) q = helpDistribute [p] q ++ distribute ps q 


-- | Converts a proposition into a rigid CNF.
--
-- Cases of interest your code has to handle for a correct CNF implemention:
-- - Literals and their Negation
-- - Connectives
-- - Double negative
-- - Negatives over connectives
--
-- Note that as the names Neg and Lit are both defined in Prop and CNF, you
-- need to use CNF.Lit or CNF.Neg to differentiate them from those defined in
-- Prop.
--
-- Hint: [[CNF.Neg p]] = !p
--
-- Why do we have a separate type for CNF instead of Prop?
-- - CNF is a rigid form of Prop; it can only ever represent formulas in CNF.
--   Prop may represent formulas in CNF, but also  other formulas. Using the
--   rigid form allows us to avoid runtime checks to see whether a Prop is in
--   CNF as needed for DPLL.

-- Tests:
-- keeps literals (and their negation) [v]
-- removes double negatives [v]
-- distributes disjuncts (and leaves conjuncts) [x]
-- applies De-Morgans law [x]
-- recursively applies all cases [x]
cnf :: Prop a -> CNF a
cnf (Lit p) = [[CNF.Lit p]]  -- keeps lit
cnf (Neg (Lit p)) = [[CNF.Neg p]]  --keeps neg lit
cnf (Neg (Neg p)) = cnf p -- removes double neg

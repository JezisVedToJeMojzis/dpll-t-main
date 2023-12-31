module CNF.Tseitin
  ( equisat
  , fresh
  ) where

import Rename
import AST.Prop
import CNF.Transform (cnf)
import CNF.Types (CNF)

import Control.Monad.State
import Control.Monad.Writer

import Debug.Trace

-- | Use this to get a fresh propositional literal.
fresh :: MonadState ID m => m (Prop ID)
fresh = do
  ident <- get
  put $ ident + 1
  return $ Lit ident

-- | Tseitins transformation
--
-- Transforms a propositional formula into an equisatisfiable CNF formula while
-- avoiding the exponential space blow-up that happens with the normal CNF
-- transformation.
--
-- Note: In Tseitin's transformation, we traverse the propositional formula
-- and introduce new names and definitions for the subexpressions. Your task is
-- to implement this transformation here. Please revisit the lecture slides and
-- make sure you thoroughly understand Tseitin's transformation before
-- attempting to implement it.
--
-- What are the Monad typeclasses used in the definition of tseitin?
-- - tseitin uses both the State and Writer interfaces. This means that we can
--   use `put`, `get` and `tell`.
--
-- What do we need these for?
-- - State: You don't need to modify the state (using put/get) directly. The
--   state is used to implement the `fresh` helper function. The `fresh` helper
--   function returns a fresh literal. You can use this to create new names for
--   subformulas.
-- - Writer: The writer is used to *accumulate* the final outcome of the tseitin
--   transformation. That is, whenver you created a definition for a subformula,
--   you can use `tell` to add it to the final CNF. Use your implementation of
--   'cnf' to transform a general proposition formula into a rigid CNF formula. 
--
-- What is the return value of tseitin?
-- - The return value is a (Prop ID), which should always be the propositional
--   variable used to represent the current formula.
-- - We don't introduce new names for literals, so you may directly return a
--   literal when encountered.
--
-- Note: The automatic tests have some requirements on the implementation.
-- - You should first get a fresh variable before recursing
-- - On binary operands, the left hand side should be recursed first
tseitin :: (MonadState ID m, MonadWriter (CNF ID) m) => Prop ID -> m (Prop ID)
tseitin (Lit p) = return (Lit p)  -- single variable, no need to transform
tseitin (Neg p) = do
  fresh_p <- fresh
  p' <- tseitin p
  tell (cnf (Neg fresh_p :|: Neg p'))  -- Add the CNF clause (¬fresh_p ∨ ¬p)
  tell (cnf (p' :|: fresh_p))  -- Add the CNF clause (p ∨ fresh_p)
  return fresh_p
tseitin (p :&: q) = do
  fresh_and <- fresh  -- Generate a fresh propositional variable fresh_and
  fresh_p <- tseitin p
  fresh_q <- tseitin q
  tell (cnf (Neg fresh_and :|: fresh_p))  -- Add the CNF clause (¬fresh_and ∨ p)
  tell (cnf (Neg fresh_and :|: fresh_q))  -- Add the CNF clause (¬fresh_and ∨ q)
  tell (cnf (Neg fresh_p :|: Neg fresh_q :|: fresh_and))  -- Add the CNF clause (¬p ∨ ¬q ∨ fresh_and)
  return fresh_and  -- Return the fresh variable for (p ∧ q)
tseitin (p :|: q) = do
  fresh_or <- fresh  -- Generate a fresh propositional variable fresh_or
  fresh_p <- tseitin p
  fresh_q <- tseitin q
  tell (cnf (Neg fresh_or :|: fresh_p :|: fresh_q))  -- Add the CNF clause (¬fresh_or ∨ p ∨ q)
  tell (cnf (Neg fresh_p :|: fresh_or))  -- Add the CNF clause (¬p ∨ fresh_or)
  tell (cnf (Neg fresh_q :|: fresh_or))  -- Add the CNF clause (¬q ∨ fresh_or)
  return fresh_or  -- Return the fresh variable for (p ∨ q)

-- tseitin :: (MonadState ID m, MonadWriter (CNF ID) m) => Prop ID -> m (Prop ID)
-- tseitin (Lit p) = return (Lit p)
-- tseitin (Neg p) = do
--   fresh_p <- fresh
--   let msg = "Neg case: p = " ++ show p ++ ", fresh_p = " ++ show fresh_p
--   traceM msg
--   tell (cnf (Neg fresh_p :|: Neg p))
--   tell (cnf (fresh_p :|: p))
--   return fresh_p
-- tseitin (p :&: q) = do
--   fresh_p <- tseitin p
--   fresh_q <- tseitin q
--   fresh_and <- fresh
--   let msg = "Conjunct case: p = " ++ show p ++ ", q = " ++ show q ++ ", fresh_p = " ++ show fresh_p ++ ", fresh_q = " ++ show fresh_q ++ ", fresh_and = " ++ show fresh_and
--   traceM msg
--   tell (cnf (Neg fresh_p :|: Neg fresh_q :|: fresh_and))
--   tell (cnf (fresh_p :|: Neg fresh_and))
--   tell (cnf (fresh_q :|: Neg fresh_and))
--   return fresh_and
-- tseitin (p :|: q) = do
--   fresh_p <- tseitin p
--   fresh_q <- tseitin q
--   fresh_or <- fresh
--   let msg = "Disjunct case: p = " ++ show p ++ ", q = " ++ show q ++ ", fresh_p = " ++ show fresh_p ++ ", fresh_q = " ++ show fresh_q ++ ", fresh_or = " ++ show fresh_or
--   traceM msg
--   tell (cnf (fresh_p :|: fresh_q :|: Neg fresh_or))
--   tell (cnf (Neg fresh_p :|: fresh_or))
--   tell (cnf (Neg fresh_q :|: fresh_or))
--   return fresh_or
  
-- | Get an equisatisfiable CNF by tseitins transformation. Renames the
-- CNF before running the transformation, such that we can create fresh
-- variables.
equisat :: Ord a => Prop a -> (CNF ID, Renames a)
equisat p = (expr, names)
  where
    expr = evalState (execWriterT tseitin') initial
    tseitin' = tseitin p' >>= tell . cnf
    (initial, p', names) = rename p

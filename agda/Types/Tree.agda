module Types.Tree where

open import Data.List.Base using (List)

-- We want to represent every possible interleaving of the threads in the dining
-- philosophers problem. An infinite rose tree [1] with branching paths at each
-- decision point seems appropriate:
--
-- > record Tree (A : Set) : Set where
-- >   coinductive
-- >   field
-- >     value
-- >       : A
-- >     children
-- >       : List (Tree A)
--
-- However, when proving properties about those interleavings, the fact that the
-- future decision points are entirely determined by the current state is
-- important. To reflect this, we use an alternate representation inspired by
-- the Nu fixed point [2].
--
-- [1] https://hackage-content.haskell.org/package/containers-0.8/docs/Data-Tree.html#t:Tree
-- [2] https://hackage.haskell.org/package/data-fix-0.3.4/docs/Data-Fix.html#t:Nu
data Tree (A : Set) : Set where
  MkTree : (A → List A) → A → Tree A

StepFun : Set → Set
StepFun A = A → List A

value : {A : Set} → Tree A → A
value (MkTree _ v) = v

stepFun : {A : Set} → Tree A → StepFun A
stepFun (MkTree f _) = f

childValues : {A : Set} → Tree A → List A
childValues (MkTree f v) = f v
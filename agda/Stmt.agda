{-# OPTIONS --guardedness #-}
module Stmt where

open import Data.Nat using (ℕ)

open import Fork using (Fork)

-- For representing Rust code fragment like
--
-- > think_randomly(1);
-- > let _guard1 = FORK_1_2.lock().unwrap();
-- > let _guard2 = FORK_5_1.lock().unwrap();
-- > eat_randomly(1);
data Stmt : Set where
  ThinkRandomly
    : ℕ → Stmt
  EatRandomly
    : ℕ → Stmt
  LockFork
    : ℕ → Fork → Stmt  -- guard number, fork

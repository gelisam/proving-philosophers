{-# OPTIONS --guardedness #-}
module TrustedCore.Stmt where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String.Base as Str using () renaming (_++_ to _+++_)

open import Syntax using (Syntax; Line)
open import TrustedCore.Fork using (Fork; MkFork; show-fork)

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
    : ℕ → ℕ → ℕ → Stmt  -- guard number, fork i, fork j

-- We have to trust that
--
-- > render-stmt (ThinkRandomly 3)
--
-- doesn't produce something non-sensical like "mutex.lock()", otherwise we will
-- be proving facts about the wrong program.
render-stmt : Stmt → Syntax
render-stmt (ThinkRandomly n)
  = Line ("think_randomly(" +++ show n +++ ");")
render-stmt (EatRandomly n)
  = Line ("eat_randomly(" +++ show n +++ ");")
render-stmt (LockFork g i j)
  = Line ( "let _guard" +++ show g
       +++ " = " +++ show-fork (MkFork i j)
       +++ ".lock().unwrap();"
         )
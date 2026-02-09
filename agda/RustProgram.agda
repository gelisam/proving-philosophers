module RustProgram where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; reverse; map; concat; _++_)
open import Data.String.Base using (String)
open import Data.String.Base as Str using () renaming (_++_ to _+++_)

import Types.Syntax
open import Types.Fork using (Fork; MkFork)
open import Types.Stmt using (ThinkRandomly; LockFork; EatRandomly)
open import Types.Thread using (Thread; MkThread)
open import Types.Program using (Program; MkProgram)

-- an Agda representation of rust/main.rs, so we can prove things about it.

threads : List Thread
threads =
  MkThread 1
    ( ThinkRandomly 1
    ∷ LockFork 1 (MkFork 1 2)
    ∷ LockFork 2 (MkFork 5 1)
    ∷ EatRandomly 1
    ∷ [] )
  ∷ MkThread 2
    ( ThinkRandomly 2
    ∷ LockFork 1 (MkFork 1 2)
    ∷ LockFork 2 (MkFork 2 3)
    ∷ EatRandomly 2
    ∷ [] )
  ∷ MkThread 3
    ( ThinkRandomly 3
    ∷ LockFork 1 (MkFork 2 3)
    ∷ LockFork 2 (MkFork 3 4)
    ∷ EatRandomly 3
    ∷ [] )
  ∷ MkThread 4
    ( ThinkRandomly 4
    ∷ LockFork 1 (MkFork 3 4)
    ∷ LockFork 2 (MkFork 4 5)
    ∷ EatRandomly 4
    ∷ [] )
  ∷ MkThread 5
    ( ThinkRandomly 5
    ∷ LockFork 1 (MkFork 4 5)
    ∷ LockFork 2 (MkFork 5 1)
    ∷ EatRandomly 5
    ∷ [] )
  ∷ []

program : Program
program = MkProgram 5 threads
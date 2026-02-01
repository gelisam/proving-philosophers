{-# OPTIONS --guardedness #-}
module Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; reverse; map; concat; _++_)
open import Data.String.Base using (String)
open import Data.String.Base as Str using () renaming (_++_ to _+++_)
open import IO.Base using (Main; run)
open import IO.Finite using (putStr)

header : String
header =
  "use std::sync::Mutex;\n\
  \use std::thread;\n\
  \use rand::Rng;\n\
  \\n\
  \fn think_randomly(philosopher_id: usize) {\n\
  \    let mut rng = rand::thread_rng();\n\
  \    let think_time = rng.gen_range(1..=10);\n\
  \    println!(\"Philosopher {} is thinking for {} seconds...\", philosopher_id, think_time);\n\
  \    thread::sleep(std::time::Duration::from_secs(think_time));\n\
  \    println!(\"Philosopher {} is done thinking.\", philosopher_id);\n\
  \}\n\
  \\n\
  \fn eat_randomly(philosopher_id: usize) {\n\
  \    let mut rng = rand::thread_rng();\n\
  \    let eat_time = rng.gen_range(1..=10);\n\
  \    println!(\"Philosopher {} is eating for {} seconds...\", philosopher_id, eat_time);\n\
  \    thread::sleep(std::time::Duration::from_secs(eat_time));\n\
  \    println!(\"Philosopher {} is done eating.\", philosopher_id);\n\
  \}\n"

-- Helper function to create indentation
indent : ℕ → String
indent zero = ""
indent (suc n) = "    " +++ indent n

-- Data types for representing Rust code structure
data Stmt : Set where
  ThinkRandomly : ℕ → Stmt
  EatRandomly : ℕ → Stmt
  LockFork : ℕ → ℕ → ℕ → Stmt  -- guard number, fork i, fork j

data Block : Set where
  MkBlock : List Stmt → Block

data Thread : Set where
  MkThread : ℕ → Block → Thread  -- philosopher id, block

-- Render functions that produce List String with indentation
render-stmt : ℕ → Stmt → List String
render-stmt ind (ThinkRandomly n) = (indent ind +++ "think_randomly(" +++ show n +++ ");\n") ∷ []
render-stmt ind (EatRandomly n) = (indent ind +++ "eat_randomly(" +++ show n +++ ");\n") ∷ []
render-stmt ind (LockFork g i j) = 
  (indent ind +++ "let _guard" +++ show g +++ " = FORK_" +++ show i +++ "_" +++ show j +++ ".lock().unwrap();\n") ∷ []

render-block : ℕ → Block → List String
render-block ind (MkBlock stmts) = concat (map (render-stmt ind) stmts)

render-threads : ℕ → List Thread → List String
render-threads ind [] = []
render-threads ind (MkThread pid (MkBlock stmts) ∷ threads) =
  (loopStart ∷ loopOpen ∷ []) ++ stmtLines ++ (loopClose ∷ spawnClose ∷ restThreads)
  where
    handleName : String
    handleName = "handle" +++ show pid
    loopStart : String
    loopStart = indent ind +++ "let " +++ handleName +++ " = thread::spawn(|| {\n"
    loopOpen : String
    loopOpen = indent (suc ind) +++ "loop {\n"
    stmtLines : List String
    stmtLines = render-block (suc (suc ind)) (MkBlock stmts)
    loopClose : String
    loopClose = indent (suc ind) +++ "}\n"
    spawnClose : String
    spawnClose = indent ind +++ "});\n"
    restThreads : List String
    restThreads = render-threads ind threads


-- Renamed from fork-declaration to indicate it produces a String (not List String)
-- static FORK_1_2: Mutex<()> = Mutex::new(());
render-fork-declaration-string : ℕ → ℕ → String
render-fork-declaration-string i j
    = "static FORK_" +++ show i
              +++ "_" +++ show j
   +++ ": Mutex<()> = Mutex::new(());\n"

-- static FORK_1_2: Mutex<()> = Mutex::new(());
-- static FORK_2_3: Mutex<()> = Mutex::new(());
-- static FORK_3_1: Mutex<()> = Mutex::new(());
fork-declarations : ℕ → List String
fork-declarations n
  = reverse
  ( render-fork-declaration-string n 1
  ∷ go n
  )
  where
    go : ℕ → List String
    go i@(suc i-1@(suc _))
      = render-fork-declaration-string i-1 i
      ∷ go i-1
    go (suc zero)
      = []
    go zero
      = []

concat-strings : List String → String
concat-strings []       = ""
concat-strings (s ∷ ss) = s +++ concat-strings ss

full-program : ℕ → String
full-program n
  = header
 +++ "\n"
 +++ concat-strings (fork-declarations n)

main : Main
main = run (putStr (full-program 5))

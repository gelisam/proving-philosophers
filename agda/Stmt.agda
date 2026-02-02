{-# OPTIONS --guardedness #-}
module Stmt where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; reverse; map; concat; _++_)
open import Data.String.Base using (String)
open import Data.String.Base as Str using () renaming (_++_ to _+++_)
open import Syntax using (Syntax; Line; Block; Indent)

-- Data types for representing Rust code structure
data Stmt : Set where
  ThinkRandomly
    : ℕ → Stmt
  EatRandomly
    : ℕ → Stmt
  LockFork
    : ℕ → ℕ → ℕ → Stmt  -- guard number, fork i, fork j

data Thread : Set where
  MkThread : ℕ → List Stmt → Thread  -- philosopher id, block

-- Render functions that produce Syntax
render-stmt : Stmt → Syntax
render-stmt (ThinkRandomly n)
  = Line ("think_randomly(" +++ show n +++ ");")
render-stmt (EatRandomly n)
  = Line ("eat_randomly(" +++ show n +++ ");")
render-stmt (LockFork g i j)
  = Line ( "let _guard" +++ show g
       +++ " = FORK_" +++ show i
              +++ "_" +++ show j
       +++ ".lock().unwrap();"
         )

render-thread : Thread → Syntax
render-thread (MkThread pid stmts)
  = Block (spawnStart ∷ loopBody ∷ spawnClose ∷ [])
  where
    handleName : String
    handleName
      = "handle" +++ show pid

    spawnStart : Syntax
    spawnStart
      = Line ("let " +++ handleName +++ " = thread::spawn(|| {")

    loopBody : Syntax
    loopBody
      = Indent (Block 
      ( Line "loop {"
      ∷ Indent (Block (map render-stmt stmts))
      ∷ Line "}"
      ∷ [] ))

    spawnClose : Syntax
    spawnClose
      = Line "});"

render-threads : List Thread → Syntax
render-threads threads
  = Block (map render-thread threads)

render-header : Syntax
render-header = Block
  ( Line "use std::sync::Mutex;"
  ∷ Line "use std::thread;"
  ∷ Line "use rand::Rng;"
  ∷ Line ""
  ∷ Line "fn think_randomly(philosopher_id: usize) {"
  ∷ Indent (Block
      ( Line "let mut rng = rand::thread_rng();"
      ∷ Line "let think_time = rng.gen_range(1..=10);"
      ∷ Line "println!(\"Philosopher {} is thinking for {} seconds...\", philosopher_id, think_time);"
      ∷ Line "thread::sleep(std::time::Duration::from_secs(think_time));"
      ∷ Line "println!(\"Philosopher {} is done thinking.\", philosopher_id);"
      ∷ [] ))
  ∷ Line "}"
  ∷ Line ""
  ∷ Line "fn eat_randomly(philosopher_id: usize) {"
  ∷ Indent (Block
      ( Line "let mut rng = rand::thread_rng();"
      ∷ Line "let eat_time = rng.gen_range(1..=10);"
      ∷ Line "println!(\"Philosopher {} is eating for {} seconds...\", philosopher_id, eat_time);"
      ∷ Line "thread::sleep(std::time::Duration::from_secs(eat_time));"
      ∷ Line "println!(\"Philosopher {} is done eating.\", philosopher_id);"
      ∷ [] ))
  ∷ Line "}"
  ∷ [] )

-- static FORK_1_2: Mutex<()> = Mutex::new(());
render-fork-declaration : ℕ → ℕ → Syntax
render-fork-declaration i j
    = Line ("static FORK_" +++ show i
               +++ "_" +++ show j
    +++ ": Mutex<()> = Mutex::new(());")

-- static FORK_1_2: Mutex<()> = Mutex::new(());
-- static FORK_2_3: Mutex<()> = Mutex::new(());
-- static FORK_3_1: Mutex<()> = Mutex::new(());
render-fork-declarations : ℕ → Syntax
render-fork-declarations n
  = Block (reverse
  ( render-fork-declaration n 1
  ∷ go n
  ))
  where
    go : ℕ → List Syntax
    go i@(suc i-1@(suc _))
      = render-fork-declaration i-1 i
      ∷ go i-1
    go (suc zero)
      = []
    go zero
      = []

render-join : Thread → Syntax
render-join (MkThread pid _)
  = Line ("handle" +++ show pid +++ ".join().unwrap();")

-- Render join statements for each thread
render-joins : List Thread → Syntax
render-joins threads
  = Block (map render-join threads)

render-program : List Thread → Syntax
render-program threads = Block
  ( render-header
  ∷ Line ""
  ∷ render-fork-declarations 5
  ∷ Line ""
  ∷ Line "fn main() {"
  ∷ Indent (Block
      ( render-threads threads
      ∷ render-joins threads
      ∷ [] ))
  ∷ Line "}"
  ∷ [] )
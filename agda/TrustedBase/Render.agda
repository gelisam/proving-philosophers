{-# OPTIONS --guardedness #-}
module TrustedBase.Render where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; reverse; map)
open import Data.String.Base as Str using (String) renaming (_++_ to _+++_)

open import Syntax using (Syntax; Line; Block; Indent)
open import Fork using (Fork; MkFork; show-fork)
open import Stmt using (Stmt; ThinkRandomly; EatRandomly; LockFork)
open import Thread using (Thread; MkThread)
open import Program using (Program; MkProgram)

-- Render a fork declaration
render-fork-declaration : Fork → Syntax
render-fork-declaration fork
    = Line ("static " +++ show-fork fork +++ ": Mutex<()> = Mutex::new(());")

-- Render a statement
render-stmt : Stmt → Syntax
render-stmt (ThinkRandomly n)
  = Line ("think_randomly(" +++ show n +++ ");")
render-stmt (EatRandomly n)
  = Line ("eat_randomly(" +++ show n +++ ");")
render-stmt (LockFork g fork)
  = Line ( "let _guard" +++ show g
       +++ " = " +++ show-fork fork
       +++ ".lock().unwrap();"
         )

-- Render a thread spawn
render-spawn-thread : Thread → Syntax
render-spawn-thread (MkThread pid stmts)
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

-- Render a thread join
render-join-thread : Thread → Syntax
render-join-thread (MkThread pid _)
  = Line ("handle" +++ show pid +++ ".join().unwrap();")

-- Render imports for the Rust program
render-imports : Syntax
render-imports = Block
  ( Line "use std::sync::Mutex;"
  ∷ Line "use std::thread;"
  ∷ Line "use rand::Rng;"
  ∷ [] )

-- Render helper functions for the Rust program
render-functions : Syntax
render-functions = Block
  ( Line "fn think_randomly(philosopher_id: usize) {"
  ∷ Indent (Block
      ( Line "let mut rng = rand::thread_rng();"
      ∷ Line "let think_time = rng.gen_range(1..=10);"
      ∷ Line "println!(\"Philosopher {} is thinking for {} seconds...\", philosopher_id, think_time);"
      ∷ Line "thread::sleep(std::time::Duration::from_secs(think_time));"
      ∷ Line "println!(\"Philosopher {} is done thinking.\", philosopher_id);"
      ∷ [] ))
  ∷ Line "}"
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

-- Render fork declarations for n forks
render-fork-declarations : ℕ → Syntax
render-fork-declarations n
  = Block (reverse
  ( render-fork-declaration (MkFork n 1)
  ∷ go n
  ))
  where
    go : ℕ → List Syntax
    go i@(suc i-1@(suc _))
      = render-fork-declaration (MkFork i-1 i)
      ∷ go i-1
    go (suc zero)
      = []
    go zero
      = []

-- Render thread spawns
render-thread-spawns : List Thread → Syntax
render-thread-spawns threads
  = Block (map render-spawn-thread threads)

-- Render thread joins
render-thread-joins : List Thread → Syntax
render-thread-joins threads
  = Block (map render-join-thread threads)

-- Render the complete program
render-program-internal : ℕ → List Thread → Syntax
render-program-internal n threads = Block
  ( render-imports
  ∷ render-fork-declarations n
  ∷ render-functions
  ∷ Line "fn main() {"
  ∷ Indent (Block
      ( render-thread-spawns threads
      ∷ render-thread-joins threads
      ∷ [] ))
  ∷ Line "}"
  ∷ [] )

-- Render a program from a Program value
render-program : Program → Syntax
render-program (MkProgram n threads) = render-program-internal n threads

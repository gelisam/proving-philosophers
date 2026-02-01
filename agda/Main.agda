{-# OPTIONS --guardedness #-}
module Main where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; reverse)
open import Data.String.Base using (String; _++_)
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

-- static FORK_1_2: Mutex<()> = Mutex::new(());
fork-declaration : ℕ → ℕ → String
fork-declaration i j
    = "static FORK_" ++ show i
              ++ "_" ++ show j
   ++ ": Mutex<()> = Mutex::new(());\n"

-- static FORK_1_2: Mutex<()> = Mutex::new(());
-- static FORK_2_3: Mutex<()> = Mutex::new(());
-- static FORK_3_1: Mutex<()> = Mutex::new(());
fork-declarations : ℕ → List String
fork-declarations n
  = reverse
  ( fork-declaration n 1
  ∷ go n
  )
  where
    go : ℕ → List String
    go i@(suc i-1@(suc _))
      = fork-declaration i-1 i
      ∷ go i-1
    go (suc zero)
      = []
    go zero
      = []

concat : List String → String
concat []       = ""
concat (s ∷ ss) = s ++ concat ss

full-program : ℕ → String
full-program n
  = header
 ++ "\n"
 ++ concat (fork-declarations n)

main : Main
main = run (putStr (full-program 5))

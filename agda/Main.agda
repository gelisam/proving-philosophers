{-# OPTIONS --guardedness #-}
module Main where

open import Data.String.Base using (String)
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


main : Main
main = run (putStr header)

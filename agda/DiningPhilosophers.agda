module DiningPhilosophers where

open import Data.String using (String; _++_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.List using (List; []; _∷_; map; foldr)
open import IO using (IO; Main; run; putStrLn)
open import Function using (_∘_)

-- AST for simplified Rust code
-- Note: This is a simplified demonstration. A complete implementation would
-- handle runtime variable references properly in the AST.
data Stmt : Set where
  -- Variable declarations
  VarDecl : String → String → Stmt
  -- Lock operation (.lock().unwrap())
  -- Expands a single Lock node to: let guard = fork.lock().unwrap();
  Lock : String → String → Stmt
  -- Sleep operation (thread::sleep(std::time::Duration::from_millis(...)))
  -- Expands a single Sleep node to full thread::sleep with Duration
  Sleep : ℕ → Stmt
  -- Print statement
  Print : String → Stmt
  -- Spawn thread
  Spawn : List Stmt → Stmt
  -- Join thread
  Join : String → Stmt
  -- If statement for conditional (simplified for demonstration)
  IfElse : ℕ → List Stmt → List Stmt → Stmt
  -- Match statement (simplified for demonstration)
  -- In a full implementation, this would reference a runtime variable
  Match : ℕ → List (ℕ × String × String) → Stmt

-- Generate Rust code from AST
generateStmt : Stmt → String
generateStmt (VarDecl name expr) = 
  "let " ++ name ++ " = " ++ expr ++ ";"
generateStmt (Lock fork guard) = 
  "let " ++ guard ++ " = " ++ fork ++ ".lock().unwrap();"
generateStmt (Sleep millis) = 
  "thread::sleep(std::time::Duration::from_millis(" ++ show millis ++ "));"
generateStmt (Print msg) = 
  "println!(\"" ++ msg ++ "\");"
generateStmt (Spawn stmts) = 
  "let handle = thread::spawn(move || {" ++ "\n" ++
  foldr (λ s acc → "    " ++ generateStmt s ++ "\n" ++ acc) "" stmts ++
  "});"
generateStmt (Join handle) = 
  handle ++ ".join().unwrap();"
generateStmt (IfElse i thenStmts elseStmts) = 
  "let (first_fork, second_fork) = if i == " ++ show i ++ " {" ++ "\n" ++
  foldr (λ s acc → "    " ++ generateStmt s ++ "\n" ++ acc) "" thenStmts ++
  "} else {" ++ "\n" ++
  foldr (λ s acc → "    " ++ generateStmt s ++ "\n" ++ acc) "" elseStmts ++
  "};"
generateStmt (Match i cases) = 
  "let (fork_left, fork_right) = match i {" ++ "\n" ++
  foldr (λ { (n , left , right) acc → 
    "    " ++ show n ++ " => (Arc::clone(&" ++ left ++ "), Arc::clone(&" ++ right ++ ")),\n" ++ acc 
  }) "    _ => unreachable!(),\n};" cases

-- Full program structure
generateProgram : String
generateProgram = 
  "use std::sync::{Arc, Mutex};" ++ "\n" ++
  "use std::thread;" ++ "\n" ++
  "\n" ++
  "fn main() {" ++ "\n" ++
  "    let fork0 = Arc::new(Mutex::new(()));" ++ "\n" ++
  "    let fork1 = Arc::new(Mutex::new(()));" ++ "\n" ++
  "    let fork2 = Arc::new(Mutex::new(()));" ++ "\n" ++
  "    let fork3 = Arc::new(Mutex::new(()));" ++ "\n" ++
  "    let fork4 = Arc::new(Mutex::new(()));" ++ "\n" ++
  "\n" ++
  "    let mut handles = vec![];" ++ "\n" ++
  "\n" ++
  "    for i in 0..5 {" ++ "\n" ++
  "        " ++ generateStmt (Match 0 
    ((0 , "fork0" , "fork1") ∷
     (1 , "fork1" , "fork2") ∷
     (2 , "fork2" , "fork3") ∷
     (3 , "fork3" , "fork4") ∷
     (4 , "fork0" , "fork4") ∷ [])) ++ "\n" ++
  "\n" ++
  "        let handle = thread::spawn(move || {" ++ "\n" ++
  "            let (first_fork, second_fork) = if i == 4 {" ++ "\n" ++
  "                (fork_right, fork_left)" ++ "\n" ++
  "            } else {" ++ "\n" ++
  "                (fork_left, fork_right)" ++ "\n" ++
  "            };" ++ "\n" ++
  "\n" ++
  "            " ++ generateStmt (Lock "first_fork" "_guard1") ++ "\n" ++
  "            " ++ generateStmt (Lock "second_fork" "_guard2") ++ "\n" ++
  "\n" ++
  "            println!(\"Philosopher {} is eating\", i);" ++ "\n" ++
  "            " ++ generateStmt (Sleep 100) ++ "\n" ++
  "            println!(\"Philosopher {} is done eating\", i);" ++ "\n" ++
  "        });" ++ "\n" ++
  "\n" ++
  "        handles.push(handle);" ++ "\n" ++
  "    }" ++ "\n" ++
  "\n" ++
  "    for handle in handles {" ++ "\n" ++
  "        handle.join().unwrap();" ++ "\n" ++
  "    }" ++ "\n" ++
  "}"

-- Main function to output the generated code
main : Main
main = run (putStrLn generateProgram)

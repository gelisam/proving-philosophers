{-# OPTIONS --guardedness #-}
module TrustedCore.Program where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; reverse; map; _++_)
open import Data.String.Base as Str using () renaming (_++_ to _+++_)

open import Syntax using (Syntax; Line; Block; Indent)
open import TrustedCore.Thread using (Thread; render-spawn-thread; render-join-thread)

-- For representing Rust code like the entirety of rust/main.rs
data Program : Set where
  MkProgram
    : ℕ  -- number of forks
    → List Thread
    → Program

-- We are not going to prove anything about the implementation of think_randomly
-- and eat_randomly, only about how often they are called, so we don't need a
-- sophisticated Agda representation of those functions, we can just use a
-- hardcoded string.
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

render-thread-spawns : List Thread → Syntax
render-thread-spawns threads
  = Block (map render-spawn-thread threads)

-- Render join statements for each thread
render-thread-joins : List Thread → Syntax
render-thread-joins threads
  = Block (map render-join-thread threads)

-- We have to trust that
--
-- > render-program (MkProgram 5 (MkThread 1 (ThinkRandomly 1 ∷ ...) ∷ ...))
--
-- doesn't produce something non-sensical like
-- "fn main() {println!(\"Hello, world!\");}", otherwise we will be proving
-- facts about the wrong program.
render-program : Program → Syntax
render-program (MkProgram n threads) = Block
  ( render-header
  ∷ Line ""
  ∷ render-fork-declarations n
  ∷ Line ""
  ∷ Line "fn main() {"
  ∷ Indent (Block
      ( render-thread-spawns threads
      ∷ render-thread-joins threads
      ∷ [] ))
  ∷ Line "}"
  ∷ [] )
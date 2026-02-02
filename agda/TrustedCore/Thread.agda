{-# OPTIONS --guardedness #-}
module TrustedCore.Thread where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.String.Base using (String)
open import Data.String.Base as Str using () renaming (_++_ to _+++_)

open import Syntax using (Syntax; Line; Block; Indent)
open import TrustedCore.Stmt using (Stmt; render-stmt)

-- For representing Rust code fragment like
--
-- > let handle1 = thread::spawn(|| {
-- >     loop {
-- >         think_randomly(1);
-- >         let _guard1 = FORK_1_2.lock().unwrap();
-- >         let _guard2 = FORK_5_1.lock().unwrap();
-- >         eat_randomly(1);
-- >     }
-- > });
data Thread : Set where
  MkThread : ℕ → List Stmt → Thread  -- philosopher id, block

-- We have to trust that
--
-- > render-spawn-thread (MkThread 1 (ThinkRandomly 1 ∷ ...))
--
-- doesn't produce something non-sensical like "mutex.lock()", otherwise we will
-- be proving facts about the wrong program.
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

render-join-thread : Thread → Syntax
render-join-thread (MkThread pid _)
  = Line ("handle" +++ show pid +++ ".join().unwrap();")

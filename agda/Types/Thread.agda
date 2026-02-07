module Types.Thread where

open import Data.Nat using (ℕ)
open import Data.List.Base using (List)

open import Types.Stmt using (Stmt)

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

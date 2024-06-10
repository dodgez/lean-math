namespace Algebra
class Zero (α : Type u) where
  zero : α

class AddSemiGroup (α : Type u) extends Add α where
  add_assoc : ∀ (a b c : α), (a + b) + c = a + (b + c)

class AddCommMagma (α : Type u) extends Add α where
  add_comm : ∀ (a b : α), a + b = b + a

class AddCommSemiGroup (α : Type u) extends AddCommMagma α, AddSemiGroup α where

class AddZeroClass (α : Type u) extends Add α, Zero α where
  add_zero : ∀ (a : α), a + Zero.zero = a
  zero_add : ∀ (a : α), Zero.zero + a = a

class AddMonoid (α : Type u) extends AddSemiGroup α, AddZeroClass α where
  nsmul : Nat -> α -> α
  nsmul_succ : ∀ (n : Nat) (a : α), nsmul n.succ a = nsmul n a + a
  nsmul_zero : ∀ (a : α), nsmul 0 a = Zero.zero

class AddCommMonoid (α : Type u) extends AddCommSemiGroup α, AddMonoid α
end Algebra

import LeanMath.Algebra

inductive N where
  | zero : N
  | succ : N -> N

namespace N
def add : N -> N -> N
  | N.zero, n => n
  | N.succ m, n => N.succ $ add m n
instance : Add N where
  add := add

theorem zero_add (a : N) : N.zero + a = a := by
  simp only [HAdd.hAdd, Add.add, add]

theorem add_succ (a b : N) : a + b.succ = (a + b).succ := by
  simp only [HAdd.hAdd, Add.add]
  induction a
  case zero =>
    simp only [add]
  case succ n ih =>
    simp only [add]
    rw [ih]

@[simp] theorem succ_add (a b : N) : (a + b).succ = a.succ + b := by
  simp only [HAdd.hAdd, Add.add, add]

@[simp] theorem add_zero (a : N) : a + N.zero = a := by
  simp only [HAdd.hAdd, Add.add]
  induction a
  case zero =>
    simp only [add]
  case succ _ ih =>
    simp only [add]
    rw [ih]

@[simp] theorem add_assoc (a b c : N) : a + b + c = a + (b + c) := by
  simp only [HAdd.hAdd, Add.add]
  induction a
  case zero =>
    simp only [add]
  case succ _ ih =>
    simp only [add]
    rw [ih]

@[simp] theorem add_comm (a b : N) : a + b = b + a := by
  induction a
  case zero =>
    simp only [zero_add, add_zero]
  case succ n ih =>
    simp only [HAdd.hAdd, Add.add, add]
    simp only [HAdd.hAdd, Add.add, add] at ih
    rw [ih]
    have : ∀ (a b : N), (a.add b).succ = a.add b.succ := by
      intro a b
      induction a
      case zero =>
        simp only [add]
      case succ _ ih =>
        simp only [add]
        rw [ih]
    apply this b n

def nsmul : Nat -> N -> N
  | Nat.succ n, a => nsmul n a + a
  | Nat.zero, _ => zero

@[simp] theorem nsmul_succ (n : Nat) (a : N) : nsmul n.succ a = nsmul n a + a := by
  simp only [nsmul]

@[simp] theorem nsmul_zero (a : N) : nsmul 0 a = zero := by
  simp only [nsmul]

instance : Algebra.AddCommMonoid N where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  nsmul := nsmul
  nsmul_succ := nsmul_succ
  nsmul_zero := nsmul_zero
  zero := N.zero
  zero_add := zero_add

instance : Algebra.AddCommSemiGroup N := Algebra.AddCommMonoid.toAddCommSemiGroup
instance : Algebra.AddMonoid N := Algebra.AddCommMonoid.toAddMonoid
instance : Algebra.AddSemiGroup N := Algebra.AddCommSemiGroup.toAddSemiGroup
instance : Algebra.AddCommMagma N := Algebra.AddCommSemiGroup.toAddCommMagma
instance : Algebra.AddZeroClass N := Algebra.AddMonoid.toAddZeroClass
instance : Algebra.Zero N := Algebra.AddZeroClass.toZero
end N

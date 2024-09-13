import Mathlib.Algebra.Group.Basic

inductive N where
  | zero : N
  | succ : N -> N

private def add : N -> N -> N
  | N.zero, n => n
  | N.succ m, n => N.succ $ add m n

instance : Add N where
  add := add

private def mul : N -> N -> N
  | N.zero, _ => N.zero
  | N.succ n, m => m + mul n m

namespace N
@[simp] theorem zero_add (a : N) : N.zero + a = a := by
  simp only [HAdd.hAdd, Add.add, add]

@[simp] theorem add_succ (a b : N) : a + b.succ = (a + b).succ := by
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
    have : ∀ (a b : N), (a + b).succ = a + b.succ := by
      intro a b
      induction a
      case zero =>
        simp only [zero_add, add_succ]
      case succ =>
        simp only [succ_add, add_succ]
    apply this b n

def nsmul : Nat -> N -> N
  | Nat.succ n, a => nsmul n a + a
  | Nat.zero, _ => zero

@[simp] theorem nsmul_succ (n : Nat) (a : N) : nsmul n.succ a = nsmul n a + a := by
  simp only [nsmul]

@[simp] theorem nsmul_zero (a : N) : nsmul 0 a = zero := by
  simp only [nsmul]

instance : AddCommMonoid N where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  nsmul := nsmul
  nsmul_succ := nsmul_succ
  nsmul_zero := nsmul_zero
  zero := N.zero
  zero_add := zero_add

@[simp] axiom succ_eq {a b : N} : a.succ = b.succ -> a = b

@[simp] theorem add_right_cancel_iff {a b c : N} : a + c = b + c ↔ a = b := by
  apply Iff.intro
  case mp =>
    intro h
    induction c
    case zero =>
      simp only [N.add_zero] at h
      simp only [h]
    case succ n ih =>
      simp only [N.add_succ] at h
      rw [ih]
      apply N.succ_eq
      exact h
  case mpr =>
    intro h
    induction c
    case zero =>
      simp only [h]
    case succ _ ih =>
      simp only [N.add_succ, ih]

instance : Mul N where
  mul := mul

@[simp] theorem mul_comm (a b : N) : a * b = b * a := by
  have mul_succ (a b : N) : mul a b.succ = a + mul a b := by
    induction a
    case zero =>
      rfl
    case succ a ih =>
      simp only [mul]
      rw [ih]
      rw [<- N.succ_add]
      repeat rw [<- N.succ_add]
      rw [<- N.add_assoc]
      rw [<- N.add_comm a b]
      rw [<- N.add_assoc]
  induction a
  case zero =>
    induction b
    case zero =>
      simp only [HMul.hMul, Mul.mul, mul]
    case succ b ih =>
      simp only [HMul.hMul, Mul.mul, mul] at *
      rw [<- ih]
      rfl
  case succ a ih =>
    induction b
    case zero =>
      simp only [HMul.hMul, Mul.mul, mul] at *
      rw [ih]
      rfl
    case succ b _ =>
      simp only [HMul.hMul, Mul.mul, mul] at *
      rw [ih]
      rw [mul_succ]
      repeat rw [<- N.succ_add]
      rw [<- N.add_assoc]
      rw [<- N.add_comm a b]
      rw [<- N.add_assoc]

@[simp] theorem zero_mul (a : N) : zero * a = zero := by
  simp only [HMul.hMul, Mul.mul, mul]

@[simp] theorem mul_zero (a : N) : a * zero = zero := by
  rw [<- N.mul_comm]
  apply zero_mul

@[simp] theorem mul_succ (a b : N) : a * succ b = a * b + a := by
  induction a
  case zero =>
    simp only [zero_mul, add_zero]
  case succ n ih =>
    simp only [HMul.hMul, Mul.mul, mul] at *
    rw [ih]
    simp only [add_succ, succ_add, add_assoc]

@[simp] theorem succ_mul (a b : N) : succ a * b = a * b + b := by
  simp only [mul_comm, mul_succ]

@[simp] theorem right_distrib (a b c : N) : (a + b) * c = a * c + b * c := by
  induction c
  case zero =>
    simp only [mul_zero, add_zero]
  case succ n ih =>
    repeat rw [mul_succ]
    rw [ih]
    rw [add_assoc]
    rw [<- add_assoc (b*n) a b]
    rw [add_comm (b*n)]
    repeat rw [<- add_assoc]

@[simp] theorem mul_assoc (a b c : N) : a * b * c = a * (b * c) := by
  induction a
  case zero =>
    simp only [HMul.hMul, Mul.mul, mul]
  case succ a ih =>
    induction b
    case zero =>
      simp only [mul_zero, zero_mul]
    case succ b _ =>
      rw [succ_mul]
      rw [right_distrib]
      rw [ih]
      simp only [succ_mul]

private def one := N.succ 0

@[simp] theorem one_mul (a : N) : one * a = a := by
  simp only [HMul.hMul, Mul.mul, mul, N.add_zero]

@[simp] theorem mul_one (a : N) : a * one = a := by
  rw [<- mul_comm]
  apply one_mul

instance : CommMonoid N where
  mul := mul
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  one := one
  one_mul := one_mul
end N

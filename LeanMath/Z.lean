import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import LeanMath.N

private def N₂ := N × N

private def eqv (n m : N₂) : Prop :=
  n.1 + m.2 = n.2 + m.1

@[simp] private theorem eqv_is_refl (x : N₂) :  eqv x x := by
  simp only [eqv, N.add_comm]

@[simp] private theorem eqv_is_symm {x y : N₂} : eqv x y -> eqv y x := by
  intro h
  simp only [eqv, N.add_comm] at *
  simp only [h]

@[simp] private theorem eqv_is_trans {x y z : N₂} : eqv x y -> eqv y z -> eqv x z := by
  intro h1
  intro h2
  simp only [eqv] at *
  apply Iff.mp $ N.add_right_cancel_iff (c := y.snd)
  have : x.fst + y.snd + z.snd = x.snd + y.fst + z.snd :=
    Iff.mpr N.add_right_cancel_iff h1
  simp only [N.add_assoc, N.add_comm z.snd]
  simp only [<- N.add_assoc]
  simp only [this]
  simp only [N.add_assoc]
  simp only [h2]
  simp only [N.add_comm]

@[simp] private theorem eqv_iseqv : Equivalence eqv := {
  refl := eqv_is_refl
  symm := eqv_is_symm
  trans := eqv_is_trans
}

private instance : Setoid N₂ where
  iseqv := eqv_iseqv
  r := eqv

def Z := Quotient instSetoidN₂
def Z.mk : N₂ -> Z := Quotient.mk instSetoidN₂

private def addN₂ : N₂ -> N₂ -> Z
  | (a, b), (c, d) => Z.mk (a + c, b + d)
private theorem addN₂_is_well_defined (a₁ b₁ a₂ b₂ : N₂) (h1 : eqv a₁ a₂) (h2 : eqv b₁ b₂) : addN₂ a₁ b₁ = addN₂ a₂ b₂ := by
  simp only [eqv, addN₂] at *
  apply Quotient.sound
  simp only [instHasEquivOfSetoid, Setoid.r, eqv]
  rw [N.add_assoc]
  rw [<- N.add_assoc b₁.fst]
  rw [N.add_comm b₁.fst]
  repeat rw [<- N.add_assoc]
  rw [h1]
  rw [N.add_assoc]
  rw [h2]
  rw [N.add_assoc]
  rw [<- N.add_assoc a₂.fst]
  rw [N.add_comm a₂.fst]
  repeat rw [<- N.add_assoc]

private def negN₂ : N₂ -> Z
  | (a, b) => Z.mk (b, a)

private theorem negN₂_is_well_defined (a b : N₂) (h : eqv a b) : negN₂ a = negN₂ b := by
  simp only [eqv, addN₂] at *
  apply Quotient.sound
  simp only [instHasEquivOfSetoid, Setoid.r, eqv]
  rw [h]

private def mulN₂ : N₂ -> N₂ -> Z
  | (a₁, a₂), (b₁, b₂) => Z.mk (a₁ * b₁ + a₂ * b₂, a₁ * b₂ + a₂ * b₁)

private theorem mulN₂_is_well_defined (a₁ b₁ a₂ b₂ : N₂) (h1 : eqv a₁ a₂) (h2 : eqv b₁ b₂) : mulN₂ a₁ b₁ = mulN₂ a₂ b₂ := by
  have swap_add (a b c : N) : a + (b + c) = b + (a + c) := by
    simp only [<- N.add_assoc a, N.add_comm a, N.add_assoc]
  apply Quotient.sound
  case _ =>
  simp only [HasEquiv.Equiv, Setoid.r, eqv] at *
  apply Iff.mp $ N.add_right_cancel_iff (c := a₂.2 * b₁.1 + a₁.1 * b₂.1 + a₂.1 * b₁.2 + a₁.2 * b₂.2)
  suffices a₁.1 * b₁.1 + a₂.2 * b₁.1 + (a₁.2 * b₁.2 + a₂.1 * b₁.2 + (a₁.2 * b₂.2 + a₂.1 * b₂.2 + (a₁.1 * b₂.1 + a₂.2 * b₂.1)))
    = a₁.1 * b₁.2 + a₁.1 * b₂.1 + (a₁.2 * b₁.1 + a₁.2 * b₂.2 + (a₂.1 * b₁.2 + a₂.1 * b₂.1 + (a₂.2 * b₁.1 + a₂.2 * b₂.2))) by
    repeat rw [N.add_assoc] at *
    simp only [swap_add, this, N.add_comm] at *
    exact this
  repeat rw [<- N.right_distrib, <- N.left_distrib]
  repeat rw [h1, h2]
  rw [<- N.add_assoc ((a₁.2 + a₂.1) * b₁.2)]
  rw [N.add_comm ((a₁.2 + a₂.1) * b₁.2)]
  rw [N.add_assoc]
  rw [<- N.add_assoc ((a₁.2 + a₂.1) * b₁.1)]
  repeat rw [<- N.left_distrib, h2, <- N.left_distrib]
  rw [N.add_comm (a₂.1 * (b₁.2 + b₂.1))]
  rw [<- N.add_assoc (a₁.2 * (b₁.2 + b₂.1))]
  rw [N.add_comm (a₁.2 * (b₁.2 + b₂.1))]
  rw [N.add_assoc]
  rw [<- N.add_assoc (a₁.1 * (b₁.2 + b₂.1))]
  rw [<- N.right_distrib a₁.1, h1]
  rw [<- N.right_distrib a₁.2]

namespace Z
def add : Z -> Z -> Z := Quotient.lift₂ addN₂ addN₂_is_well_defined

private theorem add_is_lifted_addN₂ : ∀ (x y : N₂), add (Z.mk x) (Z.mk y) = addN₂ x y := by
  intro x y
  apply Quotient.sound
  apply Equivalence.refl eqv_iseqv

instance : Add Z where
  add := add

def zero := Z.mk (N.zero, N.zero)

@[simp] theorem zero_add (a : Z) : zero + a = a := by
  have zero_works : (mk (N.zero, N.zero)) = zero := by
    rfl
  cases (Quotient.exists_rep a) with
  | intro aPos h => {
    rw [<- h]
    rw [<- zero_works]
    rw [<- mk]
    simp only [HAdd.hAdd, Add.add]
    rw [add_is_lifted_addN₂ (N.zero, N.zero) aPos]
    unfold addN₂
    let (a1, a2) := aPos
    simp
  }

@[simp] theorem add_zero (a : Z) : a + zero = a := by
  have zero_works : (mk (N.zero, N.zero)) = zero := by
    rfl
  cases (Quotient.exists_rep a) with
  | intro aPos h => {
    rw [<- h]
    rw [<- zero_works]
    rw [<- mk]
    simp only [HAdd.hAdd, Add.add]
    rw [add_is_lifted_addN₂ aPos (N.zero, N.zero)]
    unfold addN₂
    let (a1, a2) := aPos
    simp
  }

@[simp] theorem add_comm (a b : Z) : a + b = b + a := by
  cases (Quotient.exists_rep a) with
  | intro aPos h1 => {
    cases (Quotient.exists_rep b) with
    | intro bPos h2 => {
      rw [<- h1, <- h2]
      apply Quotient.sound
      simp only [N.add_comm]
      apply Equivalence.refl eqv_iseqv
    }
  }

def nsmul : Nat -> Z -> Z
  | Nat.succ n, a => nsmul n a + a
  | Nat.zero, _ => Z.zero

@[simp] theorem nsmul_succ (n : Nat) (a : Z) : nsmul n.succ a = nsmul n a + a := by
  simp only [nsmul]

@[simp] theorem nsmul_zero (a : Z) : nsmul 0 a = Z.zero := by
  simp only [nsmul]

theorem add_assoc (a b c : Z) : a + b + c = a + (b + c) := by
  cases (Quotient.exists_rep a) with
  | intro aPos h1 => {
    let (a1, a2) := aPos
    cases (Quotient.exists_rep b) with
    | intro bPos h2 => {
      let (b1, b2) := bPos
      cases (Quotient.exists_rep c) with
      | intro cPos h3 => {
        let (c1, c2) := cPos
        rw [<- h1, <- h2, <- h3]
        rw [<- Z.mk]
        apply Quotient.sound
        repeat rw [N.add_assoc]
        apply Equivalence.refl eqv_iseqv
      }
    }
  }

instance : AddCommMonoid Z where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  nsmul := nsmul
  nsmul_succ := nsmul_succ
  nsmul_zero := nsmul_zero
  zero := Z.mk (N.zero, N.zero)
  zero_add := zero_add

def neg : Z -> Z := Quotient.lift negN₂ negN₂_is_well_defined

private theorem neg_is_lifted_negN₂ : ∀ (x : N₂), neg (Z.mk x) = negN₂ x := by
  intro x
  let (x1, x2) := x
  apply Quotient.sound
  apply Equivalence.refl eqv_iseqv

instance : Neg Z where
  neg := neg

@[simp] theorem neg_add_cancel (a : Z) : -a + a = Z.zero := by
  cases Quotient.exists_rep a with
  | intro aPos h => {
    let (a1, a2) := aPos
    rw [<- h]
    rw [<- Z.mk]
    apply Quotient.sound
    rw [N.add_comm]
    rfl
  }

def zsmul : ℤ -> Z -> Z
  | (Int.negSucc n), a => -nsmul (n + 1) a
  | (Int.ofNat Nat.zero), _ => 0
  | (Int.ofNat (Nat.succ n)), a => a + (nsmul n a)

@[simp] private theorem zsmul_neg' (n : Nat) (a : Z) : zsmul (Int.negSucc n) a = -zsmul (↑n.succ) a := by
  unfold zsmul
  simp only [nsmul_succ, add_comm]

@[simp] private theorem zsmul_succ' (n : Nat) (a : Z) : zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a := by
  unfold zsmul
  simp only [Int.ofNat_eq_coe, nsmul_succ, add_comm]
  induction n
  case zero =>
    simp only [nsmul_zero]
    rfl
  case succ n _ =>
    simp only [nsmul_succ, add_comm]

@[simp] private theorem zsmul_zero' (a : Z) : zsmul 0 a = 0 := by
  rfl

instance : AddGroup Z where
  neg_add_cancel := neg_add_cancel
  zsmul := zsmul
  zsmul_neg' := zsmul_neg'
  zsmul_succ' := zsmul_succ'
  zsmul_zero' := zsmul_zero'

def mul : Z -> Z -> Z := Quotient.lift₂ mulN₂ mulN₂_is_well_defined

instance : Mul Z where
  mul := mul

theorem mul_assoc (a b c : Z) : a * b * c = a * (b * c) := by
  cases Quotient.exists_rep a with
  | intro aPos h1 =>
  cases Quotient.exists_rep b with
  | intro bPos h2 =>
  cases Quotient.exists_rep c with
  | intro cPos h3 =>
  rw [<- h1, <- h2, <- h3]
  apply Quotient.sound
  have swap_add (a b c : N) : a + (b + c) = b + (a + c) := by
    simp only [<- N.add_assoc a, N.add_comm a, N.add_assoc]
  have swap_mul (a b c : N) : a * (b * c) = b * (a * c) := by
    simp only [<- N.mul_assoc a, N.mul_comm a, N.mul_assoc]
  repeat rw [N.left_distrib, N.right_distrib]
  repeat rw [N.add_assoc]
  simp only [swap_add, N.add_comm, swap_mul, N.mul_comm]
  apply Equivalence.refl eqv_iseqv

theorem mul_comm (a b : Z) : a * b = b * a := by
  cases Quotient.exists_rep a with
  | intro aPos h1 =>
  cases Quotient.exists_rep b with
  | intro bPos h2 =>
  rw [<- h1, <- h2]
  apply Quotient.sound
  simp only [N.add_comm, N.mul_comm]
  apply Equivalence.refl eqv_iseqv

def one := Z.mk (1, 0)

theorem one_mul (a : Z) : one * a = a := by
  cases Quotient.exists_rep a with
  | intro aPos h =>
    let (a₁, a₂) := aPos
    repeat rw [<- h]
    apply Quotient.sound
    simp only [N.mul_comm, N.mul_one]
    simp only [OfNat.ofNat, One.one, Zero.zero, N.mul_one, N.add_zero, N.mul_zero]
    apply Equivalence.refl eqv_iseqv

theorem mul_one (a : Z) : a * one = a := by
  rw [mul_comm]
  apply one_mul

instance : CommMonoid Z where
  mul := mul
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  one := one
  one_mul := one_mul

theorem zero_mul (a : Z) : zero * a = 0 := by
  cases Quotient.exists_rep a with
  | intro aPos h =>
    let (a₁, a₂) := aPos
    repeat rw [<- h]
    apply Quotient.sound
    simp only [N.mul_comm]
    simp only [OfNat.ofNat, Zero.zero, N.add_zero, N.mul_zero]
    apply Equivalence.refl eqv_iseqv

theorem mul_zero (a : Z) : a * zero = 0 := by
  rw [mul_comm]
  apply zero_mul

theorem left_distrib (a b c : Z) : a * (b + c) = a * b + a * c := by
  cases Quotient.exists_rep a with
  | intro aPos h1 =>
  cases Quotient.exists_rep b with
  | intro bPos h2 =>
  cases Quotient.exists_rep c with
  | intro cPos h3 =>
  rw [<- h1, <- h2, <- h3]
  apply Quotient.sound
  have swap_add (a b c : N) : a + (b + c) = b + (a + c) := by
    simp only [<- N.add_assoc a, N.add_comm a, N.add_assoc]
  have swap_mul (a b c : N) : a * (b * c) = b * (a * c) := by
    simp only [<- N.mul_assoc a, N.mul_comm a, N.mul_assoc]
  repeat rw [N.left_distrib]
  repeat rw [N.add_assoc]
  simp only [swap_add, N.add_comm, swap_mul, N.mul_comm]
  apply Equivalence.refl eqv_iseqv

theorem right_distrib (a b c : Z) : (a + b) * c = a * c + b * c := by
  rw [mul_comm]
  rw [left_distrib]
  rw [mul_comm c, mul_comm c]

instance : CommRing Z where
  add_comm := add_comm
  add_zero := add_zero
  left_distrib := left_distrib
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  mul_zero := mul_zero
  neg_add_cancel := neg_add_cancel
  nsmul := nsmul
  nsmul_succ := nsmul_succ
  nsmul_zero := nsmul_zero
  one_mul := one_mul
  right_distrib := right_distrib
  zero_add := zero_add
  zero_mul := zero_mul
  zsmul := zsmul
  zsmul_neg' := zsmul_neg'
  zsmul_succ' := zsmul_succ'
  zsmul_zero' := zsmul_zero'
end Z

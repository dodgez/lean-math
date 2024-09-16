import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import LeanMath.Z

def NonZeroZ := {z : Z // z ≠ 0}
instance : Coe NonZeroZ Z where
  coe a := a.val

def Z₂ := Z × NonZeroZ

instance : HMul Z NonZeroZ Z where
  hMul := fun a _ => a
instance : HMul NonZeroZ Z Z where
  hMul := fun _ a => a

namespace Q
protected def eqv (n m : Z₂) : Prop :=
  n.1 * m.2 = n.2 * m.1

@[simp] theorem eqv_is_refl (x : Z₂) :  Q.eqv x x := by
  simp only [Q.eqv]
  simp only [Z.mul_comm]

@[simp] theorem eqv_is_symm {x y : Z₂} : Q.eqv x y -> Q.eqv y x := by
  intro h
  simp only [Q.eqv, Z.mul_comm] at *
  simp only [h]

@[simp] theorem eqv_is_trans {x y z : Z₂} : Q.eqv x y -> Q.eqv y z -> Q.eqv x z := by
  intro h1
  intro h2
  simp only [Q.eqv] at *
  apply Iff.mp $ Z.mul_right_cancel_iff (c := y.snd)
  have : x.fst * y.snd * z.snd = x.snd * y.fst * z.snd := by
    simp only [h1, h2, Z.mul_comm]
  simp only [Z.mul_assoc, Z.mul_comm z.snd]
  simp only [<- Z.mul_assoc]
  simp only [this]
  simp only [Z.mul_assoc]
  simp only [h2]
  simp only [Z.mul_comm]

@[simp] theorem eqv_iseqv : Equivalence Q.eqv := {
  refl := eqv_is_refl
  symm := eqv_is_symm
  trans := eqv_is_trans
}

private instance : Setoid Z₂ where
  iseqv := eqv_iseqv
  r := Q.eqv
end Q

def Q := Quotient Q.instSetoidZ₂
def Q.mk : Z₂ -> Q := Quotient.mk Q.instSetoidZ₂

namespace Q
private theorem mul_nonzero {a b : NonZeroZ} : a.val * b.val ≠ 0 := by
  by_contra h
  let h2 := @Z.mul_eq_zero a.val b.val b.2 h
  let h3 := a.2
  contradiction
def addZ₂ : Z₂ -> Z₂ -> Q
  | (a, b), (c, d) => mk (a * d + c * b, ⟨b.val * d.val, mul_nonzero⟩)
theorem addZ₂_is_well_defined (a₁ b₁ a₂ b₂ : Z₂) (h1 : Q.eqv a₁ a₂) (h2 : Q.eqv b₁ b₂) : addZ₂ a₁ b₁ = addZ₂ a₂ b₂ := by
  have swap_mul (a b c : Z) : a * (b * c) = b * (a * c) := by
    rw [<- Z.mul_assoc]
    rw [Z.mul_comm a]
    rw [Z.mul_assoc]
  simp only [addZ₂]
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv] at *
  simp only [Z.left_distrib, Z.right_distrib]
  simp only [Z.mul_assoc]
  rw [swap_mul b₁.2]
  rw [<- Z.mul_assoc]
  rw [h1]
  rw [<- Z.mul_assoc b₁.2 b₂.1]
  rw [<- h2]
  simp only [Z.mul_assoc, Z.mul_comm, swap_mul]
def add : Q -> Q -> Q := Quotient.lift₂ addZ₂ addZ₂_is_well_defined

instance : Add Q where
  add := add

private def nonZeroOne : NonZeroZ := ⟨Z.one, by
  simp only [Z.one, OfNat.ofNat, Zero.zero, Z.zero, One.one]
  intro h
  let h := Quotient.exact h
  simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.add_zero, N.one] at h
  contradiction
⟩
def zero := mk (Z.zero, nonZeroOne)
def one := mk (Z.one, nonZeroOne)
@[simp] theorem exists_pair_ne : ∃x y : Q, x ≠ y := by
    exists zero
    exists mk (Z.one, nonZeroOne)
    intro h
    let h := Quotient.exact h
    simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, Z.zero_mul, Z.mul_zero] at h
    simp only [Z.mul_one] at h
    apply nonZeroOne.2
    rw [<- h]

@[simp] theorem zero_add (a : Q) : zero + a = a := by
  cases (Quotient.exists_rep a) with
  | intro aPos h => {
    rw [<- h]
    simp only [zero]
    rw [<- mk]
    simp only [HAdd.hAdd, Add.add]
    apply Quotient.sound
    simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, Z.zero_mul, OfNat.ofNat, Zero.zero, Z.zero_add]
    simp only [Z.mul_comm aPos.1, Z.mul_assoc, Z.mul_comm aPos.1]
  }

@[simp] theorem add_zero (a : Q) : a + zero = a := by
  cases (Quotient.exists_rep a) with
  | intro aPos h => {
    rw [<- h]
    simp only [zero]
    rw [<- mk]
    simp only [HAdd.hAdd, Add.add]
    apply Quotient.sound
    simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, Z.zero_mul, OfNat.ofNat, Zero.zero, Z.add_zero]
    simp only [Z.mul_comm]
    rw [Z.mul_comm, <- Z.mul_assoc]
  }

@[simp] theorem add_comm (a b : Q) : a + b = b + a := by
  cases (Quotient.exists_rep a) with
  | intro aPos h1 => {
    cases (Quotient.exists_rep b) with
    | intro bPos h2 => {
      rw [<- h1, <- h2]
      apply Quotient.sound
      simp only [Z.add_comm, Z.mul_comm]
      apply Equivalence.refl eqv_iseqv
    }
  }

theorem add_assoc (a b c : Q) : a + b + c = a + (b + c) := by
  cases (Quotient.exists_rep a) with
  | intro aPos h1 => {
    let (a1, a2) := aPos
    cases (Quotient.exists_rep b) with
    | intro bPos h2 => {
      let (b1, b2) := bPos
      cases (Quotient.exists_rep c) with
      | intro cPos h3 => {
        have mul_swap (a b c : Z) : a * (b * c) = b * (a * c) := by
          rw [<- Z.mul_assoc]
          rw [Z.mul_comm a]
          rw [Z.mul_assoc]
        let (c1, c2) := cPos
        rw [<- h1, <- h2, <- h3]
        rw [<- mk]
        apply Quotient.sound
        simp only [Z.left_distrib, Z.right_distrib, Z.add_assoc, Z.mul_assoc, Z.mul_comm, mul_swap]
        apply Equivalence.refl eqv_iseqv
      }
    }
  }

def nsmul : Nat -> Q -> Q
  | Nat.succ n, a => nsmul n a + a
  | Nat.zero, _ => zero

@[simp] theorem nsmul_succ (n : Nat) (a : Q) : nsmul n.succ a = nsmul n a + a := by
  simp only [nsmul]

@[simp] theorem nsmul_zero (a : Q) : nsmul 0 a = zero := by
  simp only [nsmul]

def negZ₂ : Z₂ -> Q
  | (a, b) => mk (-a, b)
theorem negZ₂_is_well_defined (a b : Z₂) (h : Q.eqv a b) : negZ₂ a = negZ₂ b := by
  simp only [Q.eqv, addZ₂] at *
  apply Quotient.sound
  simp only [instHasEquivOfSetoid, Setoid.r, Q.eqv]
  have neg_mul (a b : Z) : -a * b = -(a * b) := by
    rcases (Quotient.exists_rep a) with ⟨aPos, h1⟩
    rcases (Quotient.exists_rep b) with ⟨bPos, h2⟩
    rw [<- h1, <- h2]
    apply Quotient.sound
    simp only [HasEquiv.Equiv, Setoid.r, Z.eqv]
    have swap_add (a b c : N) : a + (b + c) = b + (a + c) := by
      simp only [<- N.add_assoc a, N.add_comm a, N.add_assoc]
    repeat rw [N.add_assoc]
    simp only [N.add_comm, swap_add]
  have mul_neg (a b : Z) : a * -b = -(a * b) := by
    rw [Z.mul_comm, neg_mul, Z.mul_comm]
  rw [neg_mul, mul_neg]
  rw [h]
def neg : Q -> Q := Quotient.lift negZ₂ negZ₂_is_well_defined

instance : Neg Q where
  neg := neg

@[simp] theorem neg_add_cancel (a : Q) : -a + a = zero := by
  cases Quotient.exists_rep a with
  | intro aPos h => {
    let (a1, a2) := aPos
    rw [<- h]
    rw [<- mk]
    apply Quotient.sound
    have neg_mul (a b : Z) : -a * b = -(a * b) := by
      rcases (Quotient.exists_rep a) with ⟨aPos, h1⟩
      rcases (Quotient.exists_rep b) with ⟨bPos, h2⟩
      rw [<- h1, <- h2]
      apply Quotient.sound
      simp only [HasEquiv.Equiv, Setoid.r, Z.eqv]
      have swap_add (a b c : N) : a + (b + c) = b + (a + c) := by
        simp only [<- N.add_assoc a, N.add_comm a, N.add_assoc]
      repeat rw [N.add_assoc]
      simp only [N.add_comm, swap_add]
    rw [neg_mul]
    rw [Z.neg_add_cancel]
    simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, Z.zero_mul, Z.mul_zero]
  }

def zsmul : ℤ -> Q -> Q
  | (Int.negSucc n), a => -nsmul (n + 1) a
  | (Int.ofNat Nat.zero), _ => zero
  | (Int.ofNat (Nat.succ n)), a => a + (nsmul n a)

@[simp] private theorem zsmul_neg' (n : Nat) (a : Q) : zsmul (Int.negSucc n) a = -zsmul (↑n.succ) a := by
  unfold zsmul
  simp only [nsmul_succ, add_comm]

@[simp] private theorem zsmul_succ' (n : Nat) (a : Q) : zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a := by
  unfold zsmul
  simp only [Int.ofNat_eq_coe, nsmul_succ, add_comm]
  induction n
  case zero =>
    simp only [nsmul_zero]
  case succ n _ =>
    simp only [nsmul_succ, add_comm]

@[simp] private theorem zsmul_zero' (a : Q) : zsmul 0 a = zero := by
  rfl

instance : Field Q where
  add := add
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  exists_pair_ne := exists_pair_ne
  left_distrib := sorry
  inv := sorry
  inv_zero := sorry
  mul := sorry
  mul_assoc := sorry
  mul_comm := sorry
  mul_inv_cancel := sorry
  mul_one := sorry
  mul_zero := sorry
  neg := neg
  neg_add_cancel := neg_add_cancel
  nnqsmul := sorry
  nnqsmul_def := sorry
  nsmul := nsmul
  nsmul_succ := nsmul_succ
  nsmul_zero := nsmul_zero
  one := one
  one_mul := sorry
  qsmul := sorry
  qsmul_def := sorry
  right_distrib := sorry
  zero := zero
  zero_add := zero_add
  zero_mul := sorry
  zsmul := zsmul
  zsmul_neg' := zsmul_neg'
  zsmul_succ' := zsmul_succ'
  zsmul_zero' := zsmul_zero'
end Q

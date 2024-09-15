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
  iseqv := Q.eqv_iseqv
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
  | (a, b), (c, d) => Q.mk (a * d + c * b, ⟨b.val * d.val, mul_nonzero⟩)
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

instance : Field Q where
  add := add
  add_assoc := sorry
  add_comm := sorry
  add_zero := sorry
  exists_pair_ne := sorry
  left_distrib := sorry
  inv := sorry
  inv_zero := sorry
  mul := sorry
  mul_assoc := sorry
  mul_comm := sorry
  mul_inv_cancel := sorry
  mul_one := sorry
  mul_zero := sorry
  neg := sorry
  neg_add_cancel := sorry
  nnqsmul := sorry
  nnqsmul_def := sorry
  nsmul := sorry
  nsmul_succ := sorry
  nsmul_zero := sorry
  one := sorry
  one_mul := sorry
  qsmul := sorry
  qsmul_def := sorry
  right_distrib := sorry
  zero := sorry
  zero_add := sorry
  zero_mul := sorry
  zsmul := sorry
  zsmul_neg' := sorry
  zsmul_succ' := sorry
  zsmul_zero' := sorry
end Q

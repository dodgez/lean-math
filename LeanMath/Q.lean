import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import LeanMath.Z

def NonZeroZ := {z : Z // z ≠ 0}
instance : Coe NonZeroZ Z where
  coe a := a.val

private def Z₂ := Z × NonZeroZ

instance : HMul Z NonZeroZ Z where
  hMul := fun a _ => a
instance : HMul NonZeroZ Z Z where
  hMul := fun _ a => a

private def eqv (n m : Z₂) : Prop :=
  n.1 * m.2 = n.2 * m.1

@[simp] private theorem eqv_is_refl (x : Z₂) :  eqv x x := by
  simp only [eqv]
  simp only [Z.mul_comm]

@[simp] private theorem eqv_is_symm {x y : Z₂} : eqv x y -> eqv y x := by
  intro h
  simp only [eqv, Z.mul_comm] at *
  simp only [h]

@[simp] private theorem eqv_is_trans {x y z : Z₂} : eqv x y -> eqv y z -> eqv x z := by
  intro h1
  intro h2
  simp only [eqv] at *
  apply Iff.mp $ Z.mul_right_cancel_iff (c := y.snd)
  have : x.fst * y.snd * z.snd = x.snd * y.fst * z.snd := by
    simp only [h1, h2, Z.mul_comm]
  simp only [Z.mul_assoc, Z.mul_comm z.snd]
  simp only [<- Z.mul_assoc]
  simp only [this]
  simp only [Z.mul_assoc]
  simp only [h2]
  simp only [Z.mul_comm]

@[simp] private theorem Q.eqv_iseqv : Equivalence eqv := {
  refl := eqv_is_refl
  symm := eqv_is_symm
  trans := eqv_is_trans
}

private instance : Setoid Z₂ where
  iseqv := Q.eqv_iseqv
  r := eqv

def Q := Quotient instSetoidZ₂
def Q.mk : Z₂ -> Q := Quotient.mk instSetoidZ₂

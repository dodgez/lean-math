import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import LeanMath.N

private def N₂ := N × N

namespace Z
def eqv (n m : N₂) : Prop :=
  n.1 + m.2 = n.2 + m.1

@[simp] theorem eqv_is_refl (x : N₂) :  Z.eqv x x := by
  simp only [Z.eqv, N.add_comm]

@[simp] theorem eqv_is_symm {x y : N₂} : Z.eqv x y -> Z.eqv y x := by
  intro h
  simp only [Z.eqv, N.add_comm] at *
  simp only [h]

@[simp] theorem eqv_is_trans {x y z : N₂} : Z.eqv x y -> Z.eqv y z -> Z.eqv x z := by
  intro h1
  intro h2
  simp only [Z.eqv] at *
  apply Iff.mp $ N.add_right_cancel_iff (c := y.snd)
  have : x.fst + y.snd + z.snd = x.snd + y.fst + z.snd :=
    Iff.mpr N.add_right_cancel_iff h1
  simp only [N.add_assoc, N.add_comm z.snd]
  simp only [<- N.add_assoc]
  simp only [this]
  simp only [N.add_assoc]
  simp only [h2]
  simp only [N.add_comm]

@[simp] theorem eqv_iseqv : Equivalence Z.eqv := {
  refl := eqv_is_refl
  symm := eqv_is_symm
  trans := eqv_is_trans
}

instance : Setoid N₂ where
  iseqv := eqv_iseqv
  r := Z.eqv
end Z

def Z := Quotient Z.instSetoidN₂
def Z.mk : N₂ -> Z := Quotient.mk Z.instSetoidN₂

namespace Z
def addN₂ : N₂ -> N₂ -> Z
  | (a, b), (c, d) => Z.mk (a + c, b + d)
theorem addN₂_is_well_defined (a₁ b₁ a₂ b₂ : N₂) (h1 : Z.eqv a₁ a₂) (h2 : Z.eqv b₁ b₂) : addN₂ a₁ b₁ = addN₂ a₂ b₂ := by
  simp only [Z.eqv, addN₂] at *
  apply Quotient.sound
  simp only [instHasEquivOfSetoid, Setoid.r, Z.eqv]
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
    simp only [N.add_comm, N.add_zero]
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
    simp only [N.add_zero]
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
  zero := zero
  zero_add := zero_add

def negN₂ : N₂ -> Z
  | (a, b) => Z.mk (b, a)
theorem negN₂_is_well_defined (a b : N₂) (h : Z.eqv a b) : negN₂ a = negN₂ b := by
  simp only [Z.eqv, addN₂] at *
  apply Quotient.sound
  simp only [instHasEquivOfSetoid, Setoid.r, Z.eqv]
  rw [h]
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

def mulN₂ : N₂ -> N₂ -> Z
  | (a₁, a₂), (b₁, b₂) => Z.mk (a₁ * b₁ + a₂ * b₂, a₁ * b₂ + a₂ * b₁)
theorem mulN₂_is_well_defined (a₁ b₁ a₂ b₂ : N₂) (h1 : Z.eqv a₁ a₂) (h2 : Z.eqv b₁ b₂) : mulN₂ a₁ b₁ = mulN₂ a₂ b₂ := by
  have swap_add (a b c : N) : a + (b + c) = b + (a + c) := by
    simp only [<- N.add_assoc a, N.add_comm a, N.add_assoc]
  apply Quotient.sound
  case _ =>
  simp only [HasEquiv.Equiv, Setoid.r, Z.eqv] at *
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

@[simp] theorem add_right_cancel_iff {a b c : Z} : a + c = b + c ↔ a = b := by
  apply Iff.intro
  case mp =>
    intro h
    have : a + -c + c = b + -c + c := by
      repeat rw [add_assoc]
      rw [add_comm (-c)]
      repeat rw [<- add_assoc]
      rw [h]
    repeat rw [add_assoc] at this
    rw [neg_add_cancel] at this
    repeat rw [add_zero] at this
    exact this
  case mpr =>
    intro h
    rw [h]

@[simp] theorem neg_mul {a b : Z} : -(a * b) = -a * b := by
  cases Quotient.exists_rep a with
  | intro aPos h1 =>
  cases Quotient.exists_rep b with
  | intro bPos h2 =>
  rw [<- h1, <- h2]
  apply Quotient.sound
  simp only [N.add_comm]
  apply Equivalence.refl eqv_iseqv

@[simp] private theorem exists_reduce {a : N₂} : ∃b : N, Z.eqv a (b, N.zero) ∨ Z.eqv a (N.zero, b) := by
  let (a₁, a₂) := a
  induction a₁
  case zero =>
    exists a₂
    right
    apply eqv_is_refl
  case succ n ih1 =>
    induction a₂
    case zero =>
      exists n.succ
      left
      apply eqv_is_refl
    case succ m ih2 =>
      have eqv_succ_left {a₁ a₂ b₁ b₂ : N} : Z.eqv (a₁, a₂) (b₁, b₂) -> Z.eqv (a₁.succ, a₂) (b₁.succ, b₂) := by
        clear ih1 ih2
        intro h
        simp only [Z.eqv] at *
        rw [<- N.succ_add]
        rw [N.add_succ a₂]
        rw [h]
      have eqv_succ_right {a₁ a₂ b₁ b₂ : N} : Z.eqv (a₁, a₂) (b₁, b₂.succ) -> Z.eqv (a₁.succ, a₂) (b₁, b₂) := by
        clear eqv_succ_left ih1 ih2
        intro h
        simp only [Z.eqv] at *
        simp only [N.succ_add, N.add_succ] at *
        exact h
      rcases ih1 with ⟨b, h⟩
      cases h
      case inl h_left =>
        exists b.succ
        left
        apply eqv_succ_left h_left
      case inr h_right =>
        cases b
        case zero =>
          exists 1
          left
          apply eqv_succ_left h_right
        case succ b =>
          exists b
          right
          apply eqv_succ_right h_right

theorem exists_reduce_Z {a : Z} : ∃b : N, a = Z.mk (b, 0) ∨ a = Z.mk (0, b) := by
  cases Quotient.exists_rep a with
  | intro aPos h1 =>
  rcases @exists_reduce aPos with ⟨b, h⟩
  exists b
  cases h
  case inl h_left =>
    left
    rw [<- h1]
    apply Quotient.sound
    exact h_left
  case inr h_right =>
    right
    rw [<- h1]
    apply Quotient.sound
    exact h_right

@[simp] theorem mul_eq_zero {a b : Z} (h : b ≠ 0) : a * b = 0 -> a = 0 := by
  intro ph
  rcases @exists_reduce_Z a with ⟨n, hn⟩
  rcases @exists_reduce_Z b with ⟨m, hm⟩
  have m_not_zero : m ≠ 0 := by
    by_contra contra
    cases hm
    case inl hm =>
      rw [contra] at hm
      simp only [OfNat.ofNat, Zero.zero, zero] at h hm
      contradiction
    case inr hm =>
      rw [contra] at hm
      simp only [OfNat.ofNat, Zero.zero, zero] at h hm
      contradiction
  cases hn
  case inl hn =>
    cases hm
    case inl hm =>
      rw [hn, hm] at ph
      have : n * m = 0 := by
        dsimp [OfNat.ofNat, Zero.zero, zero] at ph
        let h := Quotient.exact ph
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul] at h
        exact h
      suffices n = 0 by
        rw [hn]
        simp only [OfNat.ofNat, Zero.zero, zero]
        apply Quotient.sound
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul]
        exact this
      apply N.mul_eq_zero m_not_zero
      exact this
    case inr hm =>
      rw [hn, hm] at ph
      have : n * m = 0 := by
        dsimp [OfNat.ofNat, Zero.zero, zero] at ph
        let h := Quotient.exact ph
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul] at h
        apply Eq.symm
        exact h
      suffices n = 0 by
        rw [hn]
        simp only [OfNat.ofNat, Zero.zero, zero]
        apply Quotient.sound
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul]
        exact this
      apply N.mul_eq_zero m_not_zero
      exact this
  case inr hn =>
    cases hm
    case inl hm =>
      rw [hn, hm] at ph
      have : n * m = 0 := by
        dsimp [OfNat.ofNat, Zero.zero, zero] at ph
        let h := Quotient.exact ph
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul] at h
        apply Eq.symm
        exact h
      suffices n = 0 by
        rw [hn]
        simp only [OfNat.ofNat, Zero.zero, zero]
        apply Quotient.sound
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul]
        apply Eq.symm
        exact this
      apply N.mul_eq_zero m_not_zero
      exact this
    case inr hm =>
      rw [hn, hm] at ph
      have : n * m = 0 := by
        dsimp [OfNat.ofNat, Zero.zero, zero] at ph
        let h := Quotient.exact ph
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul] at h
        exact h
      suffices n = 0 by
        rw [hn]
        simp only [OfNat.ofNat, Zero.zero, zero]
        apply Quotient.sound
        simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.mul_zero, N.add_zero, N.zero_add, N.zero_mul]
        apply Eq.symm
        exact this
      apply N.mul_eq_zero m_not_zero
      exact this

private def NonZeroZ := {z : Z // z ≠ 0}
private instance : Coe NonZeroZ Z where
  coe a := a.val

private def Z₂ := Z × NonZeroZ

@[simp] theorem mul_right_cancel_iff {a b : Z} {c : NonZeroZ} : a * c = b * c ↔ a = b := by
  apply Iff.intro
  case mp =>
    intro h
    have : a * c - b * c = 0 := by
      apply Iff.mp $ Z.add_right_cancel_iff (c := (b * c.val))
      simp only [OfNat.ofNat, Zero.zero, Z.zero_add]
      simp only [HSub.hSub, Sub.sub, SubNegMonoid.sub', Z.add_assoc, Z.neg_add_cancel, Z.add_zero]
      exact h
    have : (a - b) * c = 0 := by
      simp only [HSub.hSub, Sub.sub, SubNegMonoid.sub', Z.neg_mul, <- Z.right_distrib] at this
      simp only [HSub.hSub, Sub.sub, SubNegMonoid.sub']
      exact this
    have : a - b = 0 := by
      apply mul_eq_zero (b := c.val)
      exact c.property
      exact this
    have : a = b := by
      apply Iff.mp $ Z.add_right_cancel_iff (c := -b)
      simp only [HSub.hSub, Sub.sub, SubNegMonoid.sub'] at this
      rw [Z.add_comm b]
      rw [Z.neg_add_cancel]
      exact this
    exact this
  case mpr =>
    intro h
    rw [h]
end Z

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

def nonZeroOne : NonZeroZ := ⟨Z.one, by
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

@[simp] theorem add_assoc (a b c : Q) : a + b + c = a + (b + c) := by
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

instance : AddCommMonoid Q where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  nsmul := nsmul
  nsmul_succ := nsmul_succ
  nsmul_zero := nsmul_zero
  zero := zero
  zero_add := zero_add

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

def mulZ₂ : Z₂ -> Z₂ -> Q
  | (a₁, a₂), (b₁, b₂) => mk (a₁ * b₁, ⟨(a₂ * b₂ : Z), mul_nonzero⟩)
theorem mulZ₂_is_well_defined (a₁ b₁ a₂ b₂ : Z₂) (h1 : Q.eqv a₁ a₂) (h2 : Q.eqv b₁ b₂) : mulZ₂ a₁ b₁ = mulZ₂ a₂ b₂ := by
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv] at *
  have swap_mul (a b c : Z) : a * (b * c) = b * (a * c) := by
    simp only [<- Z.mul_assoc a, Z.mul_comm a, Z.mul_assoc]
  repeat rw [Z.mul_assoc]
  rw [swap_mul b₁.1]
  rw [<- Z.mul_assoc]
  rw [h1, h2]
  rw [Z.mul_assoc]
  simp only [swap_mul, Z.mul_comm]
def mul : Q -> Q -> Q := Quotient.lift₂ mulZ₂ mulZ₂_is_well_defined

instance : Mul Q where
  mul := mul

@[simp] theorem mul_assoc (a b c : Q) : a * b * c = a * (b * c) := by
  rcases Quotient.exists_rep a with ⟨aPos, h1⟩
  rcases Quotient.exists_rep b with ⟨bPos, h2⟩
  rcases Quotient.exists_rep c with ⟨cPos, h3⟩
  rw [<- h1, <- h2, <- h3]
  apply Quotient.sound
  have swap_mul (a b c : Z) : a * (b * c) = b * (a * c) := by
    simp only [<- Z.mul_assoc a, Z.mul_comm a, Z.mul_assoc]
  simp only [swap_mul, Z.mul_comm]
  apply Equivalence.refl eqv_iseqv

@[simp] theorem mul_comm (a b : Q) : a * b = b * a := by
  rcases Quotient.exists_rep a with ⟨aPos, h1⟩
  rcases Quotient.exists_rep b with ⟨bPos, h2⟩
  rw [<- h1, <- h2]
  apply Quotient.sound
  simp only [Z.mul_comm]
  apply Equivalence.refl eqv_iseqv

@[simp] theorem one_mul (a : Q) : one * a = a := by
  rcases Quotient.exists_rep a with ⟨aPos, h1⟩
  rw [<- h1, one, nonZeroOne]
  let (a₁, a₂) := aPos
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv]
  simp only [Z.one_mul, Z.mul_comm, Z.mul_one]

@[simp] theorem mul_one (a : Q) : a * one = a := by
  rw [mul_comm]
  apply one_mul

instance : CommMonoid Q where
  mul := mul
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  one := one
  one_mul := one_mul

@[simp] theorem zero_mul (a : Q) : zero * a = 0 := by
  cases Quotient.exists_rep a with
  | intro aPos h =>
    let (a₁, a₂) := aPos
    repeat rw [<- h]
    apply Quotient.sound
    simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, Z.zero_mul, Z.mul_zero]
    simp only [OfNat.ofNat, Zero.zero, Z.zero_mul]

@[simp] theorem mul_zero (a : Q) : a * zero = 0 := by
  rw [mul_comm]
  apply zero_mul

@[simp] theorem left_distrib (a b c : Q) : a * (b + c) = a * b + a * c := by
  rcases Quotient.exists_rep a with ⟨aPos, h1⟩
  rcases Quotient.exists_rep b with ⟨bPos, h2⟩
  rcases Quotient.exists_rep c with ⟨cPos, h3⟩
  rw [<- h1, <- h2, <- h3]
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, Z.left_distrib, Z.right_distrib]
  have swap_mul (a b c : Z) : a * (b * c) = b * (a * c) := by
    simp only [<- Z.mul_assoc a, Z.mul_comm a, Z.mul_assoc]
  simp only [Z.mul_comm, swap_mul]

@[simp] theorem right_distrib (a b c : Q) : (a + b) * c = a * c + b * c := by
  rw [mul_comm]
  rw [left_distrib]
  rw [mul_comm c, mul_comm c]

def invZ₂ (z : Z₂) : Q :=
  if h : (Z.decEq z.fst Z.zero).decide then
    zero
  else
    mk (z.snd, ⟨z.fst, by
      simp only [decide_eq_true_eq, ne_eq] at *
      simp only [OfNat.ofNat, Zero.zero]
      exact h⟩)
theorem invZ₂_is_well_defined (a b : Z₂) (h : Q.eqv a b) : invZ₂ a = invZ₂ b := by
  let (a₁, a₂) := a
  let (b₁, b₂) := b
  unfold invZ₂
  simp
  match (Z.decEq a₁ Z.zero) with
  | rhs1 =>
  match (Z.decEq b₁ Z.zero) with
  | rhs2 =>
    simp
    by_cases a₁ = Z.zero
    case pos aTheorem =>
      simp only [aTheorem, ↓reduceDIte]
      have : b₁ = Z.zero := by
        by_contra b₁NotZero
        simp only [Q.eqv, aTheorem, Z.zero_mul] at h
        have : b₁ = Z.zero := by
          apply @Z.mul_eq_zero b₁ ↑a₂ a₂.2
          apply Eq.symm
          rw [Z.mul_comm]
          exact h
        contradiction
      simp only [this, ↓reduceDIte]
    case neg aTheorem =>
      simp only [aTheorem, ↓reduceDIte]
      have : b₁ ≠ Z.zero := by
        by_contra b₁Zero
        simp only [Q.eqv] at h
        rw [b₁Zero] at h
        simp only [Z.mul_zero] at h
        let  a₁Zero := @Z.mul_eq_zero a₁ ↑b₂ b₂.2 h
        contradiction
      simp only [this, ↓reduceDIte]
      apply Quotient.sound
      simp only [HasEquiv.Equiv, Setoid.r, Q.eqv] at *
      apply Eq.symm
      exact h
def inv : Q -> Q := Quotient.lift invZ₂ invZ₂_is_well_defined

@[simp] theorem inv_zero : inv zero = zero := by
  rfl

@[simp] theorem mul_inv_cancel (a : Q) (h : a ≠ zero) : a * inv a = one := by
  rcases Quotient.exists_rep a with ⟨aPos, h₂⟩
  simp only [one, <- h₂]
  simp only [<- h₂] at h
  let (a₁, a₂) := aPos
  have : a₁ ≠ Z.zero := by
    by_contra h₃
    rcases Quotient.exists_rep a₁ with ⟨aPos2, h₄⟩
    simp only [Z.zero, <- h₄] at h₃
    let eqvZero := Quotient.exact h₃
    simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, Z.eqv, N.add_zero] at eqvZero
    let contra := h.elim
    have : ⟦(a₁, a₂)⟧ = zero := by
      apply Quotient.sound
      simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, nonZeroOne, Z.mul_one, Z.mul_zero]
      rw [<- h₄]
      simp only [OfNat.ofNat, Zero.zero, Z.zero]
      apply Quotient.sound
      simp only [HasEquiv.Equiv, Setoid.r, Z.eqv, N.add_zero]
      exact eqvZero
    apply contra this
  have : invZ₂ (a₁, a₂) = mk (a₂, ⟨a₁, this⟩) := by
    unfold invZ₂
    simp only [decide_eq_true_eq, ne_eq]
    simp only [this, decide_False, Bool.false_eq_true, ↓reduceDIte]
  unfold inv
  simp
  rw [this]
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, nonZeroOne, Z.mul_one, Z.mul_comm]

def natCast : Nat -> Q
  | Nat.zero => zero
  | Nat.succ n => one + natCast n
instance : NatCast Q where
  natCast := natCast
@[simp] theorem natCast_succ (n : Nat) : NatCast.natCast (n + 1) = NatCast.natCast n + one := by
  simp only [NatCast.natCast, natCast, add_comm]
@[simp] theorem natCast_zero : NatCast.natCast 0 = zero := by
  simp only [NatCast.natCast, natCast]

def intCast : Int -> Q
  | Int.negSucc n => -natCast n.succ
  | Int.ofNat n => natCast n
instance : IntCast Q where
  intCast := intCast
@[simp] theorem intCast_ofNat (n : Nat) : (IntCast.intCast $ Int.ofNat n) = (NatCast.natCast : Nat -> Q) n := by
  simp only [IntCast.intCast, NatCast.natCast, intCast]
@[simp] theorem intCast_negSucc (n : Nat) : (IntCast.intCast $ Int.negSucc n) = - (NatCast.natCast : Nat -> Q) n.succ := by
  simp only [IntCast.intCast, NatCast.natCast, intCast]

def ratCast (q : ℚ) : Q :=
  (Int.cast q.num : Q) * (Nat.cast q.den : Q).inv
instance : RatCast Q where
  ratCast := ratCast
instance : Div Q where
  div := fun a b => a * b.inv
@[simp] theorem ratCast_def (q : ℚ) : (Rat.cast : ℚ -> Q) q = ((Int.cast : Int -> Q ) q.num) / ((Nat.cast : Nat -> Q) q.den) := by
  simp only [Rat.cast, RatCast.ratCast] at *
  simp only [ratCast, HDiv.hDiv, Div.div]

def qsmul (q₁ : ℚ) (q₂ : Q) : Q := ratCast q₁ * q₂
@[simp] theorem qsmul_def (a : ℚ) (x : Q) : qsmul a x = ratCast a * x := by
  simp only [qsmul]

def nnratCast (q : ℚ≥0) : Q :=
  (Int.cast q.num : Q) * (Nat.cast q.den : Q).inv
instance : NNRatCast Q where
  nnratCast := nnratCast
@[simp] theorem nnratCast_def (q : ℚ≥0) : (NNRat.cast : ℚ≥0 -> Q) q = ((Int.cast : Int -> Q ) q.num) / ((Nat.cast : Nat -> Q) q.den) := by
  simp only [NNRat.cast, NNRatCast.nnratCast] at *
  simp only [nnratCast, HDiv.hDiv, Div.div]

def nnqsmul (q₁ : ℚ≥0) (q₂ : Q) : Q := nnratCast q₁ * q₂
@[simp] theorem nnqsmul_def (q : ℚ≥0) (a : Q) : nnqsmul q a = nnratCast q * a := by
  simp only [nnqsmul]

instance : Field Q where
  add := add
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  div_eq_mul_inv := by
    intro a b
    simp only [HDiv.hDiv, Div.div]
  exists_pair_ne := exists_pair_ne
  left_distrib := left_distrib
  intCast := intCast
  intCast_negSucc := intCast_negSucc
  intCast_ofNat := intCast_ofNat
  inv := inv
  inv_zero := inv_zero
  mul := mul
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_inv_cancel := mul_inv_cancel
  mul_one := mul_one
  mul_zero := mul_zero
  natCast := natCast
  natCast_succ := natCast_succ
  natCast_zero := natCast_zero
  neg := neg
  neg_add_cancel := neg_add_cancel
  nnqsmul := nnqsmul
  nnqsmul_def := nnqsmul_def
  nnratCast := nnratCast
  nnratCast_def := nnratCast_def
  nsmul := nsmul
  nsmul_succ := nsmul_succ
  nsmul_zero := nsmul_zero
  one := one
  one_mul := one_mul
  qsmul := qsmul
  qsmul_def := qsmul_def
  ratCast := ratCast
  ratCast_def := ratCast_def
  right_distrib := right_distrib
  zero := zero
  zero_add := zero_add
  zero_mul := zero_mul
  zsmul := zsmul
  zsmul_neg' := zsmul_neg'
  zsmul_succ' := zsmul_succ'
  zsmul_zero' := zsmul_zero'
end Q

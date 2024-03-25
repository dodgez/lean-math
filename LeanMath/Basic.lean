import Mathlib.Data.Int.Basic

inductive N : Type where
  | zero : N
  | next : N -> N

namespace N
def ofNat (n : Nat) : N :=
  match n with
  | 0 => N.zero
  | Nat.succ m => next $ ofNat m

instance : OfNat N n where
  ofNat := ofNat n

def toNat : N -> Nat
  | zero => 0
  | next n => 1 + toNat n

def compare : N -> N -> Ordering
  | zero, zero => Ordering.eq
  | zero, next _ => Ordering.lt
  | next _, zero => Ordering.gt
  | next n, next m => n.compare m

def add : N → N → N
  | zero, k => k
  | next n, k => next (n.add k)

def toString (n : N) : String :=
  s!"{n.toNat}"

instance : Add N where
  add := add

instance : ToString N where
  toString := toString

instance : Ord N where
  compare := compare

def orderingToString : Ordering -> String
  | Ordering.lt => "lt"
  | Ordering.eq => "eq"
  | Ordering.gt => "gt"

instance : ToString Ordering where
  toString := orderingToString

axiom add_zero (a : N) : a + zero = a
axiom add_next (a b : N) : a + next b = next (a + b)

theorem zero_add (a : N) : zero + a = a := by
  induction a
  case zero => {
    rw [add_zero]
  }
  case next n ih => {
    rw [add_next]
    rw [ih]
  }

theorem next_add {a b : N} : next a + b = next (a + b) := by
  induction b
  case zero => {
    repeat rw [add_zero]
  }
  case next n ih => {
    rw [add_next, ih, add_next]
  }

theorem next_eq_add_one (a : N) : next a = a + next zero := by
  induction a
  case zero => {
    rw [add_next]
    rw [add_zero]
  }
  case next n ih => {
    rw [next_add, ih]
  }

theorem add_comm (a b : N) : a + b = b + a := by
  induction b
  case zero => {
    rw [add_zero, zero_add]
  }
  case next n ih => {
    rw [add_next, ih, next_add]
  }

theorem add_assoc (a b c : N) : a + b + c = a + (b + c) := by
  induction c
  case zero => {
    rw [add_zero, add_zero]
  }
  case next n ih => {
    rw [add_next, add_next, add_next]
    rw [ih]
  }

axiom next_implies_eq (a b : N) (h : next a = next b) : a = b

theorem add_right_cancel (a b c : N) (h : a + c = b + c) : a = b := by
  induction c
  case zero => {
    repeat rw [add_zero] at h
    exact h
  }
  case next ih => {
    repeat rw [add_next] at h
    rw [ih]
    apply next_implies_eq
    exact h
  }

def toInt : N -> Int
  | 0 => 0
  | next n => 1 + toInt n

instance : AddMonoid N where
  add := add
  add_zero := add_zero
  zero_add := zero_add
  add_assoc := add_assoc

def mul : N -> N -> N
  | 0, _ => 0
  | next n, m => m + mul n m

theorem one_eq_next_zero : 1 = next 0 := by
  unfold OfNat.ofNat
  unfold instOfNatN
  simp
  repeat unfold ofNat
  rfl

instance : Mul N where
  mul := mul

theorem mul_zero (a : N) : a * 0 = 0 := by
  induction a
  case zero => {
    unfold HMul.hMul
    unfold instHMul
    unfold Mul.mul
    unfold instMulN
    unfold mul
    rfl
  }
  case next n ih => {
    unfold HMul.hMul
    unfold instHMul
    unfold Mul.mul
    unfold instMulN
    unfold mul
    simp
    unfold HMul.hMul at ih
    unfold instHMul at ih
    unfold Mul.mul at ih
    unfold instMulN at ih
    unfold mul
    cases n with
      | zero => {
        simp
      }
      | next m => {
        simp
        simp at ih
        unfold mul at ih
        unfold OfNat.ofNat at ih
        unfold OfNat.ofNat
        unfold instOfNatN at ih
        unfold instOfNatN
        unfold ofNat at ih
        unfold ofNat
        rw [zero_add] at ih
        exact ih
      }
  }

private theorem mul_case_zero (a : N) : a * zero = 0 := by
  have : a * zero = a * 0 := by
    unfold OfNat.ofNat
    unfold instOfNatN
    unfold ofNat
    rfl
  rw [this]
  apply mul_zero

theorem zero_mul (a : N) : 0 * a = 0 := by
  unfold HMul.hMul
  unfold instHMul
  unfold Mul.mul
  unfold instMulN
  unfold mul
  unfold OfNat.ofNat
  unfold instOfNatN
  unfold ofNat
  simp

private theorem case_zero_mul (a : N) : zero * a = 0 := by
  have : zero * a = 0 * a := by
    unfold OfNat.ofNat
    unfold instOfNatN
    unfold ofNat
    rfl
  apply this

theorem one_mul (a : N) : 1 * a = a := by
  unfold HMul.hMul
  unfold instHMul
  simp
  unfold Mul.mul
  unfold instMulN
  unfold mul
  rw [one_eq_next_zero]
  simp
  unfold OfNat.ofNat
  unfold instOfNatN
  simp
  unfold ofNat
  unfold mul
  unfold OfNat.ofNat
  unfold instOfNatN
  simp
  unfold ofNat
  rw [add_zero]

theorem mul_add (a b c : N) : a * (b + c) = a * b + a * c := by
  induction a
  case zero => {
    apply case_zero_mul
  }
  case next n ih => {
    unfold HMul.hMul
    unfold HMul.hMul at ih
    unfold instHMul
    unfold instHMul at ih
    unfold Mul.mul
    unfold Mul.mul at ih
    unfold instMulN
    unfold instMulN at ih
    unfold mul
    simp at ih
    rw [ih]
    rw [add_assoc]
    rw [add_comm c]
    rw [add_assoc]
    rw [add_comm (mul n c)]
    repeat rw [<- add_assoc]
  }

theorem mul_next (a b : N) : a * next b = a * b + a := by
  induction a
  case zero => {
    repeat rw [case_zero_mul]
    unfold OfNat.ofNat
    unfold instOfNatN
    unfold ofNat
    rw [zero_add]
  }
  case next n ih => {
    unfold HMul.hMul
    unfold HMul.hMul at ih
    unfold instHMul
    unfold instHMul at ih
    unfold Mul.mul
    unfold Mul.mul at ih
    unfold instMulN
    unfold instMulN at ih
    unfold mul
    simp at ih
    rw [ih]
    rw [next_eq_add_one, next_eq_add_one n]
    rw [add_assoc]
    rw [add_comm (next zero)]
    repeat rw [<- add_assoc]
  }

theorem add_mul (a b c : N) : (a + b) * c = a * c + b * c := by
  induction c
  case zero => {
    repeat rw [mul_case_zero]
    simp
  }
  case next n ih => {
    repeat rw [mul_next]
    rw [ih]
    rw [add_assoc]
    rw [<- add_assoc (b*n) a b]
    rw [add_comm (b*n)]
    repeat rw [<- add_assoc]
  }

theorem next_mul (a b : N) : next a * b = a * b + b := by
  rw [next_eq_add_one]
  rw [add_mul]
  have : 1 = next zero := by
    unfold OfNat.ofNat
    unfold instOfNatN
    unfold ofNat
    unfold ofNat
    rfl
  rw [<- this]
  rw [one_mul]

theorem mul_comm (a b : N) : a * b = b * a := by
  induction a
  case zero => {
    rw [case_zero_mul, mul_case_zero]
  }
  case next n ih => {
    rw [mul_next]
    rw [next_mul]
    rw [ih]
  }

theorem mul_one (a : N) : a * 1 = a := by
  rw [mul_comm]
  apply one_mul

theorem mul_assoc (a b c : N) : a * b * c = a * (b * c) := by
  induction a
  case zero => {
    repeat rw [case_zero_mul]
    rw [zero_mul]
  }
  case next n ih => {
    repeat rw [next_mul]
    rw [add_mul]
    rw [ih]
  }

instance : Monoid N where
  one := ofNat 1
  mul := mul
  mul_one := mul_one
  one_mul := one_mul
  mul_assoc := mul_assoc

instance : LT N where
  lt := fun a => fun b => ∃ c, a = b + N.next c

instance : LE N where
  le := fun a => fun b => ∃ c, a + c = b

private theorem le_next : (a b : N) -> a ≤ b -> a ≤ next b := by
  intro a b
  intro h
  unfold LE.le at h
  unfold instLEN at h
  simp at h
  cases h with
  | intro c h => {
    unfold LE.le
    unfold instLEN
    simp
    use c + 1
    rw [next_eq_add_one]
    rw [one_eq_next_zero]
    unfold OfNat.ofNat
    unfold instOfNatN
    unfold ofNat
    rw [<- add_assoc]
    rw [h]
  }

theorem le_total : (a b : N) -> a ≤ b ∨ b ≤ a := by
  intro a b
  induction b
  case zero => {
    induction a
    case zero => {
      left
      unfold LE.le
      unfold instLEN
      simp
      use zero
      rw [add_zero]
    }
    case next n _ => {
      right
      unfold LE.le
      unfold instLEN
      simp
      use next n
      rw [zero_add]
    }
  }
  case next n ih => {
    induction a
    case zero => {
      left
      unfold LE.le
      unfold instLEN
      simp
      use next n
      rw [zero_add]
    }
    case next m _ => {
      cases ih with
      | inl ih => {
        left
        apply le_next (next m) n ih
      }
      | inr ih => {
        unfold LE.le at ih
        unfold instLEN at ih
        simp at ih
        cases ih with
        | intro c ch => {
          cases c with
          | zero => {
            rw [add_zero] at ch
            symm at ch
            left
            unfold LE.le
            unfold instLEN
            simp
            use 1
            rw [ch]
            rw [next_eq_add_one]
            unfold OfNat.ofNat
            unfold instOfNatN
            repeat unfold ofNat
            rfl
          }
          | next c1 => {
            right
            unfold LE.le
            unfold instLEN
            simp
            use c1
            rw [next_eq_add_one]
            rw [add_assoc]
            rw [add_comm (next zero)]
            rw [<- next_eq_add_one]
            exact ch
          }
        }
      }
    }
  }
end N

def zeq (n : Prod N N) (m : Prod N N) : Prop :=
  n.1 + m.2 = n.2 + m.1

theorem zeq_is_refl (x : N × N) : zeq x x := by
  unfold zeq
  rw [N.add_comm x.fst x.snd]

theorem zeq_is_symm : zeq x y -> zeq y x := by
  intro h
  rw [zeq] at h ⊢
  apply Eq.symm
  rw [N.add_comm]
  rw [N.add_comm y.fst]
  exact h

theorem zeq_is_trans : zeq x y -> zeq y z -> zeq x z := by
  intro h1
  intro h2
  rw [zeq] at h1 h2 ⊢
  have h3 : x.fst + y.snd + y.fst + z.snd = x.snd + y.fst + y.snd + z.fst := by
    rw [h1, N.add_assoc, h2]
    rw [<- N.add_assoc]
  repeat rw [N.add_assoc] at h3
  rw [N.add_comm y.fst] at h3
  rw [N.add_comm y.snd] at h3
  rw [N.add_comm y.snd z.fst] at h3
  rw [<- N.add_assoc y.fst z.fst y.snd] at h3
  rw [N.add_comm y.fst z.fst] at h3
  repeat rw [<- N.add_assoc] at h3
  rw [N.add_assoc] at h3
  rw [N.add_assoc (x.snd + z.fst) y.fst y.snd] at h3
  apply N.add_right_cancel (x.fst + z.snd) (x.snd + z.fst) (y.fst + y.snd) h3

def zeq_iseqv : Equivalence zeq := {
  refl := zeq_is_refl
  symm := zeq_is_symm
  trans := zeq_is_trans
}

def N₂ := Prod N N
def ZSetoid : Setoid N₂ := { r := zeq, iseqv := zeq_iseqv }
def Z := Quotient ZSetoid

namespace Z
def lift {β : Sort v} := @Quotient.lift N₂ β ZSetoid
def mk : N₂ -> Z := @Quotient.mk N₂ ZSetoid

example : mk (3, 1) = mk (4, 2) := by
  unfold mk
  apply Quotient.sound
  have h : zeq (3, 1) (4, 2) := by
    unfold zeq
    simp
    have : (3 + 2 : N) = (1 + 4 : N) := by
      repeat rw [OfNat.ofNat]
      repeat rw [N.instOfNatN]
      simp
      repeat rw [N.ofNat]
      repeat rw [N.add_next, N.next_add]
      rw [N.add_zero, N.zero_add]
    exact this
  apply h

instance : OfNat Z n where
  ofNat := mk (OfNat.ofNat n, 0)

private def addN₂ : N₂ -> N₂ -> Z
  | (a1, a2), (b1, b2) => mk (a1 + b1, a2 + b2)
private theorem addN₂Invariant : ∀ (a₁ b₁ a₂ b₂ : N₂), zeq a₁ a₂ -> zeq b₁ b₂ → addN₂ a₁ b₁ = addN₂ a₂ b₂ := by
  intro a₁ b₁ a₂ b₂
  intro h1
  intro h2
  let (a11, a12) := a₁
  let (b11, b12) := b₁
  let (a21, a22) := a₂
  let (b21, b22) := b₂
  unfold addN₂
  simp
  unfold zeq at h1
  simp at h1
  unfold zeq at h2
  simp at h2
  unfold mk
  unfold ZSetoid
  apply Quot.sound
  simp
  unfold zeq
  simp
  rw [N.add_assoc]
  rw [<- N.add_assoc b11]
  rw [N.add_comm b11]
  repeat rw [<- N.add_assoc]
  rw [h1]
  rw [N.add_assoc]
  rw [h2]
  rw [N.add_assoc]
  rw [<- N.add_assoc a21]
  rw [N.add_comm a21]
  repeat rw [<- N.add_assoc]

def lift₂ {β : Sort u} := @Quotient.lift₂ N₂ N₂ β ZSetoid ZSetoid

def add := lift₂ addN₂ addN₂Invariant
private theorem add_is_lifted_addN₂ : ∀ (x y : N₂), add (mk x) (mk y) = addN₂ x y := by
  intro x y
  let (x1, x2) := x
  let (y1, y2) := y
  unfold addN₂
  simp
  apply Quotient.sound
  unfold HasEquiv.Equiv
  unfold instHasEquiv
  simp
  unfold Setoid.r
  unfold ZSetoid
  simp
  unfold zeq
  simp
  rw [N.add_comm]

instance : Add Z where
  add := add

private def negN₂ : N₂ -> Z
  | (a1, a2) => mk (a2, a1)
private theorem negInvariant : ∀(a b : N₂), zeq a b -> (negN₂ a) = (negN₂ b) := by
  intro (a1, a2) (b1, b2)
  unfold negN₂
  unfold zeq
  simp
  intro h
  unfold mk
  apply Quotient.sound
  unfold HasEquiv.Equiv
  unfold instHasEquiv
  simp
  unfold Setoid.r
  unfold ZSetoid
  simp
  unfold zeq
  simp
  symm
  exact h

def neg := lift negN₂ negInvariant
instance : Neg Z where
  neg := neg

private theorem neg_is_lifted_negN₂ : ∀ (a : N₂), negN₂ a = neg (mk a) := by
  intro a
  let (a1, a2) := a
  unfold negN₂
  simp
  apply Quotient.sound
  unfold HasEquiv.Equiv
  unfold instHasEquiv
  unfold Setoid.r
  unfold ZSetoid
  simp
  unfold zeq
  simp
  rw [N.add_comm]

private def toIntN₂ : N₂ -> Int
  | (n, m) => n.toInt - m.toInt

-- This is an axiom until I learn how to prove better but it is a consequence of the straight-forward integer encoding
private theorem N.toIntInvariant
  : ∀ (a1 a2 b1 b2 : N),
    zeq (a1, a2) (b1, b2) -> a1.toInt + b2.toInt = a2.toInt + b1.toInt := by
    sorry

private def toStringN₂ : N₂ -> String := toString ∘ toIntN₂
private theorem toStringN₂Invariant : ∀ (a b : N₂), zeq a b -> toStringN₂ a = toStringN₂ b := by
  intro (a1, a2) (b1, b2)
  intro h
  unfold toStringN₂
  simp
  have toIntN₂Invariant : toIntN₂ (a1, a2) = toIntN₂ (b1, b2) := by
    unfold toIntN₂
    simp
    apply @Int.add_left_cancel b2.toInt (a1.toInt - a2.toInt) (b1.toInt - b2.toInt)
    apply @Int.add_left_cancel a2.toInt (b2.toInt + (a1.toInt - a2.toInt)) (b2.toInt + (b1.toInt - b2.toInt))
    repeat rw [Int.sub_eq_add_neg]
    repeat rw [Int.add_assoc]
    rw [Int.add_comm b2.toInt]
    rw [Int.add_comm a1.toInt]
    rw [Int.add_comm b1.toInt]
    rw [<- Int.add_assoc b2.toInt]
    rw [Int.add_right_neg]
    repeat rw [<- Int.add_assoc]
    rw [Int.add_right_neg]
    rw [Int.zero_add, Int.add_zero]
    apply N.toIntInvariant
    exact h
  rw [toIntN₂Invariant]

def toString := lift toStringN₂ toStringN₂Invariant
instance : ToString Z where
  toString := toString

theorem add_zero (a : Z) : add a (0 : Z) = a := by
  have zero_works : (mk (0, 0)) = (0 : Z) := by
    unfold OfNat.ofNat
    unfold instOfNatZ
    simp
    rw [N.instOfNatN]
    simp
  cases (Quotient.exists_rep a) with
  | intro aPos h => {
    rw [<- h]
    rw [<- zero_works]
    rw [<- mk]
    rw [add_is_lifted_addN₂ aPos (0, 0)]
    unfold addN₂
    let (a1, a2) := aPos
    simp
  }

theorem zero_add (a : Z) : add (0 : Z) a = a := by
  have zero_works : (mk (0, 0)) = (0 : Z) := by
    unfold OfNat.ofNat
    unfold instOfNatZ
    simp
    rw [N.instOfNatN]
    simp
  cases (Quotient.exists_rep a) with
  | intro aPos h => {
    rw [<- h]
    rw [<- zero_works]
    rw [<- mk]
    rw [add_is_lifted_addN₂ (0, 0) aPos]
    unfold addN₂
    let (a1, a2) := aPos
    simp
  }

theorem add_assoc (a b c : Z) : add (add a b) c = add a (add b c) := by
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
        rw [<- mk]
        repeat rw [add_is_lifted_addN₂]
        unfold addN₂
        simp
        repeat rw [add_is_lifted_addN₂]
        unfold addN₂
        simp
        repeat rw [N.add_assoc]
      }
    }
  }

instance : AddMonoid Z where
  add := add
  add_zero := add_zero
  zero_add := zero_add
  add_assoc := add_assoc

theorem add_left_neg (a : Z) : -a + a = 0 := by
  unfold HAdd.hAdd
  unfold instHAdd
  unfold Add.add
  unfold instAddZ
  simp
  cases (Quotient.exists_rep a) with
  | intro aPos h1 => {
    let ((a1, a2) : N₂) := aPos
    rw [<- h1]
    have : mk (a2, a1) = -(mk (a1, a2)) := by
      symm
      unfold Neg.neg
      unfold instNegZ
      simp
      rw [<- neg_is_lifted_negN₂]
      unfold negN₂
      simp
    have same_space : @Quotient.mk N₂ ZSetoid (a1, a2) = mk (a1, a2) := by
      unfold mk
      simp
    rw [same_space]
    rw [<- this]
    rw [add_is_lifted_addN₂]
    unfold addN₂
    simp
    unfold mk
    apply Quotient.sound
    unfold HasEquiv.Equiv
    unfold instHasEquiv
    unfold Setoid.r
    unfold ZSetoid
    simp
    unfold zeq
    simp
    rw [N.add_comm]
  }

instance : AddGroup Z where
  add_left_neg := add_left_neg

private theorem exists_simple_Z : ∀ (a : Z), ∃ (b : N), a = mk (b, 0) ∨ a = mk (0, b) := by
  intro a
  cases (Quotient.exists_rep a) with
  | intro aPair h => {
    let (a1, a2) := aPair
    cases N.le_total a1 a2 with
    | inl h1 => {
      unfold LE.le at h1
      unfold N.instLEN at h1
      simp at h1
      cases h1 with
      | intro b h1 => {
        suffices zeq (0, b) (a1, a2) by
          use b
          right
          unfold mk
          rw [<- h]
          apply Quotient.sound
          unfold HasEquiv.Equiv
          unfold instHasEquiv
          unfold Setoid.r
          unfold ZSetoid
          unfold zeq
          simp
          exact h1
        unfold zeq
        simp
        symm
        rw [N.add_comm]
        exact h1
      }
    }
    | inr h1 => {
      unfold LE.le at h1
      unfold N.instLEN at h1
      simp at h1
      cases h1 with
      | intro b h1 => {
        suffices zeq (b, 0) (a1, a2) by
          use b
          left
          unfold mk
          rw [<- h]
          apply Quotient.sound
          unfold HasEquiv.Equiv
          unfold instHasEquiv
          unfold Setoid.r
          unfold ZSetoid
          unfold zeq
          simp
          symm
          exact h1
        unfold zeq
        simp
        symm
        rw [N.add_comm]
        symm
        exact h1
      }
    }
  }

def mulN₂ : N₂ -> N₂ -> Z
  | (N.next a1, N.zero), (N.next b1, N.zero) => mk (N.next a1 * N.next b1, 0)
  | (N.zero, N.next a2), (N.next b1, N.zero) => mk (0, N.next a2 * N.next b1)
  | (N.next a1, N.zero), (N.zero, N.next b2) => mk (0, N.next a1 * N.next b2)
  | (N.zero, N.next a2), (N.zero, N.next b2) => mk (N.next a2 * N.next b2, 0)
  | (a1, a2), (b1, b2) => mk (0, 0)

instance : Monoid Z where
  mul := sorry
  mul_one := sorry
  one_mul := sorry
  mul_assoc := sorry

instance : Ring Z where
  add_comm := sorry
  add_left_neg := add_left_neg
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
end Z

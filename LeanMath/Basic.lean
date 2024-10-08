import LeanMath.N
import LeanMath.Z
import LeanMath.Q

def ofNat : Nat -> N
  | Nat.zero => N.zero
  | Nat.succ n => N.succ $ ofNat n
instance : OfNat N n where
  ofNat := ofNat n

def two_neq_zero : Z.mk (2, 0) ≠ 0 := by
  by_contra this
  simp only [OfNat.ofNat, Zero.zero, ofNat, Z.zero] at this
  let this := Quotient.exact this
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, N.add_zero] at this
  contradiction
def four_neq_zero : Z.mk (4, 0) ≠ 0 := by
  by_contra this
  simp only [OfNat.ofNat, Zero.zero, ofNat, Z.zero] at this
  let this := Quotient.exact this
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, N.add_zero] at this
  contradiction
def two: NonZeroZ := ⟨Z.mk (2, 0), two_neq_zero⟩
def four: NonZeroZ := ⟨Z.mk (4, 0), four_neq_zero⟩
example : Q.mk (Z.mk (1, 0), two) = Q.mk (Z.mk (2, 0), four) := by
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, two, four]
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv]
  simp only [OfNat.ofNat, ofNat, N.mul_zero, N.zero_mul, N.add_zero, N.zero_add]
  repeat rw [N.succ_mul, N.mul_succ]
  simp only [N.zero_mul, N.add_zero, N.zero_add]
  repeat rw [<- N.succ_add, <- N.add_succ]
  simp only [N.zero_add]
  rfl

example : Q.mk (Z.mk (1, 0), two) + Q.mk (Z.mk (2, 0), four) = Q.mk (two, two) := by
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv, two, four]
  apply Quotient.sound
  simp only [HasEquiv.Equiv, Setoid.r, Q.eqv]
  simp only [OfNat.ofNat, ofNat, N.mul_zero, N.zero_mul, N.add_zero, N.zero_add]
  simp only [HMul.hMul, Mul.mul, N.mul]
  simp only [N.add_comm, N.add_succ, N.add_zero, Z.eqv_is_refl]

def toStringN : N -> String
    | N.zero => "0"
    | N.succ n => "succ " ++ toStringN n
instance : ToString N where
  toString := toStringN
#eval N.zero.succ

def toStringN₂ : N × N -> String
  | (a, b) => s!"{ToString.toString a} - {ToString.toString b}"
instance : ToString Z where
  toString := Quotient.lift toStringN₂ sorry
#eval! Z.mk (N.zero.succ, N.zero)

def toStringZ₂ : Z₂ -> String
  | (a, b) => s!"({ToString.toString a}) / ({ToString.toString b.val})"
instance : ToString Q where
  toString := Quotient.lift toStringZ₂ sorry
#eval! Q.one

#eval! Q.invZ₂ (Z.one + Z.one, Q.nonZeroOne)
#eval! Q.invZ₂ (Z.zero, Q.nonZeroOne)
#eval! Q.inv $ Q.mk (Z.one + Z.one, Q.nonZeroOne)
#eval! Q.inv $ Q.mk (Z.zero, Q.nonZeroOne)

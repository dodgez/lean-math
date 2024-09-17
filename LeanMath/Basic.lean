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

def coeN : N -> Nat
  | N.zero => Nat.zero
  | N.succ n => Nat.succ $ coeN n
instance : Coe N Nat where
  coe := coeN

def coeN₂ (a : N × N) : Int := coeN a.fst - coeN a.snd
theorem coeN₂_is_well_defined (a b : N × N) (h : Z.eqv a b) : coeN₂ a = coeN₂ b := sorry
def coeZ : Z -> Int := Quotient.lift coeN₂ coeN₂_is_well_defined

def coeZ₂ (a : Z₂) : Rat := coeZ a.fst / coeZ a.snd
theorem coeZ₂_is_well_defined (a b : Z₂) (h : Q.eqv a b) : coeZ₂ a = coeZ₂ b := sorry
def coeQ : Q -> Rat := Quotient.lift coeZ₂ coeZ₂_is_well_defined
instance : Coe Q Rat where
  coe := coeQ

instance : ToString Q where
  toString a := ToString.toString $ (Coe.coe a : Rat)

#eval! coeQ $ Q.inv $ Q.mk (Z.one + Z.one, Q.nonZeroOne)
#eval! Q.one

#eval! Q.invZ₂ (Z.one + Z.one, Q.nonZeroOne)
#eval! Q.invZ₂ (Z.zero, Q.nonZeroOne)
#eval! Q.inv $ Q.mk (Z.one + Z.one, Q.nonZeroOne)
#eval! Q.inv $ Q.mk (Z.zero, Q.nonZeroOne)

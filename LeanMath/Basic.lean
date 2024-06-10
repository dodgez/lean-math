import LeanMath.N

namespace N
def toNat : N -> Nat
  | zero => 0
  | succ n => (toNat n).succ

-- def toString : N -> String
--   | N.zero => "0"
--   | N.succ n => "succ " ++ toString n
instance : ToString N where
  toString := toString ∘ toNat

instance : HMul Nat N N where
  hMul := N.nsmul

theorem toNatRespectsSucc (n : N) : n.succ.toNat = Nat.succ n.toNat := by
  simp only [toNat]

theorem toNatRespectsAddition (n m : N) : (n + m).toNat = n.toNat + m.toNat := by
  induction n
  case zero =>
    simp only [zero_add, toNat, Nat.zero_add]
  case succ n ih =>
    simp only [HAdd.hAdd, Add.add, add]
    simp only [HAdd.hAdd, Add.add] at ih
    rw [toNatRespectsSucc]
    rw [ih, toNatRespectsSucc]
    simp only [Nat.add_eq, Nat.succ_add]

theorem toNatRespectsNsMul (n : Nat) (m : N) : (N.nsmul n m).toNat = n * m.toNat := by
  induction n
  case zero =>
    simp [nsmul, toNat]
  case succ n ih =>
    simp [nsmul]
    have (a b : N) : (a + b).toNat = a.toNat + b.toNat := by
      induction a
      case zero =>
        simp only [zero_add, toNat, Nat.zero_add]
      case succ =>
        rw [<- succ_add]
        simp only [toNat, toNatRespectsAddition, Nat.succ_add]
    simp [this]
    rw [ih]
    simp [Nat.add_mul]

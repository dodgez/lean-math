import LeanMath.N

def r : (N × N) -> (N × N) -> Prop
  | (n1, m1), (n2, m2) => n1 + m2 = n2 + m1

@[simp] axiom N.add_right_cancel : ∀ (a b c : N), a + c = b + c ↔ a = b
#check Nat.add_right_cancel
#check Nat.add_right_cancel_iff

instance : Equivalence r where
  refl := by
    simp only [r, implies_true]
  symm := by
    intro x y
    simp only [r]
    intro h
    rw [h]
  trans := by
    intro x y z
    intro h1 h2
    simp [r]
    simp [r] at h1 h2

instance : Setoid (N × N) where
  iseqv := instEquivalenceProdNR
  r := r


def Z := Quotient instSetoidProdN
def Z.mk : (N × N) -> Z := Quotient.mk instSetoidProdN
#check Z.mk (N.zero, N.zero)

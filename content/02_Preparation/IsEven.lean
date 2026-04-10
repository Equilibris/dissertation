def IsEven.Shape (P : Nat → Prop) : Prop :=
  P 0 ∧ ∀ n, P n → P (n + 2)
def IsEven (n : Nat) : Prop :=
  ∀ P, IsEven.Shape P → P n
def IsEven.z : IsEven 0 := fun P hP => hP.left
def IsEven.ss n (h : IsEven n) : IsEven (n+2) :=
  fun P hP => hP.right n (h P hP)

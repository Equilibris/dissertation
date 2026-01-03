import Sme.EquivP

open Sme

universe u

def f (A : Type u) : MvPFunctor 1 where
  A := PUnit
  B | .unit => !![A]

instance {A} : EquivP 1 (A → ·) (f A) := ⟨{
  toFun f := f.snd .fz
  invFun f := ⟨.unit, fun | .fz => f⟩
  left_inv _ := by
    simp
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    funext i v
    rcases i with (_|_|_)
    simp
  right_inv _ := funext fun _ => rfl
}⟩


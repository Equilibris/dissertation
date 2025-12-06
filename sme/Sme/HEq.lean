import Mathlib.Logic.Basic

universe u v

theorem castFn
    {A : Type u} {B C : A → Type v}
    {eq : ((v : A) → B v) = ((v : A) → C v)}
    {v : ((v : A) → B v)}
    (eq₂ : ∀ z, B z = C z) {z}
    : (cast eq v) z = cast (eq₂ z) (v z) := by
  apply eq_of_heq
  refine (heq_cast_iff_heq _ _ _).mpr ?_
  apply dcongr_heq (by rfl)
  · rintro x _ rfl; exact (eq₂ x).symm
  intro _ _
  exact cast_heq eq v

theorem dcastFn
    {A A' : Type u} {B : A → Type v} {C : A' → Type v}
    {eq : ((v : A) → B v) = ((v : A') → C v)}
    {v : ((v : A) → B v)}
    (eq₂ : A' = A)
    (eq₃ : ∀ a b, a ≍ b → B a = C b) {z}
    : (cast eq v) z = cast (eq₃ _ _ (cast_heq eq₂ z)) (v (cast eq₂ z)) := by
  apply eq_of_heq
  refine (heq_cast_iff_heq _ _ _).mpr ?_
  apply dcongr_heq
  · exact (cast_heq eq₂ z).symm
  · exact fun _ _ heq => (eq₃ _ _ (HEq.symm heq)).symm
  intro _ _
  exact cast_heq eq v

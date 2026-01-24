import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.DepRewrite

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

theorem dcastFn_push_arg
    {A A' : Type u} {B : A → Type v}
    (eq₂ : A' = A)
    (eq₁ : ((v : A) → B v) = ((v : A') → B (cast eq₂ v)))
    {v : ((v : A) → B v)} {z}
    : (cast eq₁ v) z = v (cast eq₂ z) := by
  subst eq₂
  rfl

theorem cast_sigma_congr {α α' : Type u} {β : α → Type u} {γ : α' → Type u} (fst : α) (snd : β fst)
    (pa : α = α')
    (pb : β ≍ γ)
    : cast (by subst pa pb; rfl) (Sigma.mk fst snd)
    = Sigma.mk (cast pa fst) (cast (by subst pa pb; rfl : β fst = γ (cast pa fst)) snd) := by
  subst pa pb
  rfl
theorem cast_sigma_snd {α : Type _} {β γ : α → Type _} (fst : α) (snd : β fst)
    {p : β = γ}
    : cast (congr rfl p) (Sigma.mk fst snd) = Sigma.mk fst (cast (congr p rfl) snd) := by
  subst p
  rfl

theorem hfunext_iff
    {α α' : Type u}
    {β : α → Type v} {β' : α' → Type v}
    {f : (a : α) → β a} {f' : (a : α') → β' a}
    (h : α = α')
    (h' : ∀ a a', a ≍ a' → β a ≍ β' a')
    : (∀ (a : α) (a' : α'), a ≍ a' → f a ≍ f' a') ↔ f ≍ f' where
  mp := Function.hfunext h
  mpr v := by
    subst h
    simp only [heq_eq_eq, forall_eq']
    intro a
    have teq := type_eq_of_heq v
    have := (cast_eq_iff_heq (e := teq)).mpr v
    rw! [←this]
    have := dcastFn (eq := teq) (v := f) rfl
    rw [this]
    case eq₃ =>
      rintro a b rfl
      exact eq_of_heq <| h' a a (.refl _)
    simp


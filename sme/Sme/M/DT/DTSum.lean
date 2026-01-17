import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
import Sme.Vec
import Mathlib.Tactic.MinImports

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {α β : Type u} {n : Nat}

def DTSum : MvPFunctor 2 where
  A := ULift Bool
  B := fun
    | .up .true   => !![PUnit, PEmpty]
    | .up .false  => !![PEmpty, PUnit]

instance DTSum.eqSum : EquivP 2 Sum DTSum where
  equiv := {
    toFun
      | ⟨.up .true, v⟩ => .inr (v (.fs .fz) .unit)
      | ⟨.up .false, v⟩ => .inl (v .fz .unit)
    invFun
      | .inl v => ⟨.up .false, fun | .fs .fz, h => h.elim | .fz, h => v⟩
      | .inr v => ⟨.up .true,  fun | .fs .fz, h => v | .fz, h => h.elim⟩
    right_inv
      | .inl _ | .inr _ => rfl
    left_inv := by
      rintro ⟨(_|_), h⟩
      <;> refine Sigma.ext rfl <| heq_of_eq ?_
      <;> funext i h
      <;> rcases i with (_|_|_|_)
      <;> rcases h with (_|_)
      <;> rfl
  }

-- TODO: Is this some categorical object
instance DTSum.uEqSum : EquivP 2 Sum DTSum.uLift where
  equiv := {
    toFun
      | ⟨.up <| .up .true, v⟩ => .inr (v (.fs .fz) (.up .unit))
      | ⟨.up <| .up .false, v⟩ => .inl (v .fz (.up .unit))
    invFun
      | .inl v => ⟨.up <| .up .false, fun | .fs .fz, h => h.down.elim | .fz, h => v⟩
      | .inr v => ⟨.up <| .up .true,  fun | .fs .fz, h => v | .fz, h => h.down.elim⟩
    right_inv
      | .inl _ | .inr _ => rfl
    left_inv := by
      rintro ⟨(_|_), h⟩
      <;> refine Sigma.ext rfl <| heq_of_eq ?_
      <;> funext i h
      <;> rcases i with (_|_|_|_)
      <;> rcases h with (_|_)
      <;> rfl
  }

namespace DTSum

def cont {α} (v : α .fz) : DTSum α :=
  ⟨.up .false, fun | .fs .fz, e => e.elim | .fz, .unit => v⟩

def recall {α} (v : α <| .fs .fz) : DTSum α :=
  ⟨.up .true,  fun | .fz, e => e.elim | .fs .fz, .unit => v⟩

@[simp]
theorem cont_fst {α : TypeVec _} {v : α .fz} : (cont v).fst = .up .false := rfl
@[simp]
theorem recall_fst {α : TypeVec _} {v : α <| .fs .fz} : (recall v).fst = .up .true := rfl

@[simp]
theorem map_cont {α β v} (f : α ⟹ β) : f <$$> cont v = cont (f .fz v) := by
  change Sigma.mk _ _ = Sigma.mk _ _ 
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext u v
  rcases u with (_|_|_|_)
  <;> rcases v with (_|_)
  rfl

@[simp]
theorem map_recall {α β v} (f : α ⟹ β) : f <$$> recall v = recall (f (.fs .fz) v) := by
  change Sigma.mk _ _ = Sigma.mk _ _ 
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext u v
  rcases u with (_|_|_|_)
  <;> rcases v with (_|_)
  rfl

def elim {α β} (l : α .fz → β) (r : α (.fs .fz) → β) : DTSum α → β
  | ⟨.up .false, f⟩ => l <| f .fz .unit
  | ⟨.up .true, f⟩ =>  r <| f (.fs .fz) .unit

@[simp]
theorem elim_cont {α : TypeVec _} {β} (l : α .fz → β) (r : α (.fs .fz) → β) (v : α .fz)
    : elim l r (cont v) = l v := rfl
@[simp]
theorem elim_recall {α : TypeVec _} {β} (l : α .fz → β) (r : α (.fs .fz) → β) (v : α (.fs .fz))
    : elim l r (recall v) = r v := rfl

def equiv {α : TypeVec 2} : DTSum α ≃ (α <| .fs .fz) ⊕ (α <| .fz) where
  toFun := fun
    | ⟨.up .true,  v⟩ => .inl (v (.fs .fz) .unit)
    | ⟨.up .false, v⟩ => .inr (v (.fz) .unit)
  invFun := fun
    | .inl v => recall v
    | .inr v => cont v
  left_inv := by
    rintro (_|_)
    <;> refine Sigma.ext rfl <| heq_of_eq ?_
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> cases h
    <;> simp [cont, recall]
  right_inv := fun | .inl _ | .inr _ => rfl

def equiv' {α β} : DTSum !![α, β] ≃ α ⊕ β where
  toFun := fun
    | ⟨.up .true,  v⟩ => .inl (v (.fs .fz) .unit)
    | ⟨.up .false, v⟩ => .inr (v (.fz) .unit)
  invFun := fun
    | .inl v => recall v
    | .inr v => cont v
  left_inv := by
    rintro (_|_)
    <;> refine Sigma.ext rfl <| heq_of_eq ?_
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> cases h
    <;> simp [cont, recall]
  right_inv := fun | .inl _ | .inr _ => rfl

def lift : NatIso (uLift.{u, v} DTSum) DTSum where
  equiv := (calc
    _ ≃ _ := uEqSum.equiv
    _ ≃ _ := eqSum.equiv.symm)
  nat' x := by
    rcases x with ⟨_|_, x⟩
    <;> refine Sigma.ext (by rfl) <| heq_of_eq ?_
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> rcases h with (_|_)
    <;> rfl

end Sme.DTSum


import Mathlib.Control.Functor.Multivariate

universe u v

open scoped MvFunctor
structure NatIso {n} (P Q : outParam (TypeVec.{v} n → Type u)) [MvFunctor P] [MvFunctor Q] where
  equiv : ∀ {α}, P α ≃ Q α
  nat' {α β} {f : α ⟹ β} (x : P α) : f <$$> equiv x = equiv (f <$$> x)

namespace NatIso

variable {n} {P Q R : TypeVec n → Type u} [MvFunctor P] [MvFunctor Q] [MvFunctor R]
    {α β : TypeVec n}
    {f : α ⟹ β}

instance : CoeFun (NatIso P Q) (fun _ => {α : TypeVec n} → P α → Q α) where
  coe := (·.equiv)

instance : Coe (NatIso P Q) (P α ≃ Q α) where
  coe := (·.equiv)

variable (natiso : NatIso P Q) {p : P α} {q : Q α}

@[simp] theorem abbr_eq : natiso.equiv = (natiso : P α ≃ Q α) := rfl

theorem symm' : f <$$> natiso.equiv.symm q = natiso.equiv.symm (f <$$> q) := calc
  _ = natiso.equiv.symm (natiso.equiv (f <$$> natiso.equiv.symm q))   := by simp
  _ = natiso.equiv.symm (f <$$> natiso.equiv (natiso.equiv.symm q))   := by rw [nat']
  _ = natiso.equiv.symm (f <$$> q)                                    := by simp

def symm : NatIso Q P where
  equiv := natiso.equiv.symm
  nat' _ := symm' natiso

theorem nat : f <$$> natiso p = natiso (f <$$> p) := natiso.nat' _
theorem symm_nat : f <$$> natiso.symm q = natiso.symm (f <$$> q) := natiso.symm.nat

def trans (natiso' : NatIso Q R) : NatIso P R where
  equiv := natiso.equiv.trans natiso'.equiv
  nat' := by simp [nat]

end NatIso


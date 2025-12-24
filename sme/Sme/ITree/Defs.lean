import Sme.EquivP
import Sme.M.HpLuM
import Sme.M.DT

universe u v

variable (E : Type u → Type u)

namespace Sme.ITree

inductive Base (ρ R : Type _)
  | tau (r : ρ)
  | ret (t : R)
  | vis {A : Type u} (e : E A) (k : A → ρ)

namespace Base

variable {E}

def map {ρ ρ' R R'} (f : ρ → ρ') (g : R → R') : Base E ρ R → Base E ρ' R'
  | .tau t => .tau (f t)
  | .ret r => .ret (g r)
  | .vis e k => .vis e (f ∘ k)

@[simp]
theorem map_map {ρ ρ₁ ρ₂ R R₁ R₂}
    {f₁ : ρ → ρ₁} {f₂ : ρ₁ → ρ₂}
    {g₁ : R → R₁} {g₂ : R₁ → R₂}
    : {v : Base E _ _}
    → (v.map f₁ g₁).map f₂ g₂ = v.map (f₂ ∘ f₁) (g₂ ∘ g₁) 
  | .tau _ | .ret _ | .vis _ _ => rfl

end Base

inductive PHBase
  | tau
  | ret
  | vis (A : Type u) (e : E A)

def PBase : MvPFunctor.{u + 1} 2 where
  A := PHBase E
  B | .ret => !![PUnit, PEmpty]
    | .tau => !![PEmpty, PUnit]
    | .vis A _ => !![PEmpty, PLift A]

-- 2 does not work !?
instance equivB {E} : EquivP (1 + 1) (Base E) (PBase E) := ⟨{
  toFun
    | ⟨.tau, v⟩ => .tau (v .fz .unit)
    | ⟨.ret, v⟩ => .ret (v (.fs .fz) .unit)
    | ⟨.vis A e, v⟩ => .vis e (v .fz ∘ PLift.up)
  invFun
    | .tau v => ⟨.tau, fun | .fz, _ => v | .fs .fz, e => e.elim⟩
    | .ret v => ⟨.ret, fun | .fz, v => v.elim | .fs .fz, _ => v⟩
    | .vis (A := A) e k =>
      ⟨.vis A e, fun | .fz => k ∘ PLift.down | .fs .fz => PEmpty.elim⟩
  left_inv v := by
    rcases v with ⟨⟨_⟩|⟨_⟩|⟨A, e⟩, v⟩
    <;> refine Sigma.ext (by rfl) <| heq_of_eq ?_
    <;> simp
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> rcases h with ⟨h⟩
    <;> rfl
  right_inv | .tau _ | .ret _ | .vis _ _ => rfl
}⟩

end ITree

-- I should be able to detach R and have it reside in v instead but this will require work
def ITree (R : Type (u + 1)) := HpLuM (ITree.PBase E) !![R]

namespace ITree

def PFunc (A B : Type _ → Type _) := ∀ z, A z → B z

infix:100 " ↝ " => PFunc

variable {E} {R : Type _}

def dest : ITree E R → Base E (ITree E R) R := HpLuM.destE
def mk (v : Base E (ITree E R) R) : ITree E R :=
  HpLuM.mkE (show _ from v)

@[simp] theorem dest_mk {v : ITree E R} : mk (dest v) = v := HpLuM.destE_mkE
@[simp] theorem mk_dest {v : Base E (ITree E R) R} : dest (mk v) = v := HpLuM.mkE_destE

def tau (t : ITree E R) : ITree E R := .mk <| .tau t
def ret (r : R) : ITree E R := .mk <| .ret r
def vis {A} (e : E A) (c : A → ITree E R) : ITree E R := .mk <| .vis e c

@[simp]
theorem dest_tau {t : ITree E R} : dest (tau t) = .tau t := by simp [mk, tau, dest]
@[simp]
theorem dest_ret {r : R} : dest (ret r) = .ret (E := E) r := by simp [mk, ret, dest]
@[simp]
theorem dest_vis {A} {e : E A} {c : A → ITree E R} : dest (vis e c) = .vis e c := by
  simp [mk, vis, dest]

def corec {β} (f : β → Base E β R) : β → ITree E R :=
  HpLuM.corec (match f · with
    | .ret r => ⟨.up .ret, fun | .fz, h => h.down.elim | .fs .fz, _ => .up r⟩
    | .tau t => ⟨.up .tau, fun | .fz, _ => .up t | .fs .fz, h => h.down.elim⟩
    | .vis e c => ⟨.up (.vis _ e), fun | .fz, v => .up (c v.down.down) | .fs .fz, h => h.down.elim⟩
  )

@[simp]
theorem dest_corec {β g} (gen : β → Base E β R)
    : (corec gen g).dest = (gen g).map (corec gen) id := by
  dsimp [corec, dest, HpLuM.destE]
  rw [HpLuM.dest_corec, ←corec]
  cases gen g
  <;> simp [EquivP.equiv, Base.map, MvPFunctor.uLift_down]
  · rfl
  · rfl
  · funext i
    rfl

#check HpLuM.corec_roll
theorem corec_roll {α β v}
    (f : α → β)
    (g : β → Base E α R)
    : corec (g ∘ f) v = corec (.map f id ∘ g) (f v) := by sorry

@[ext 100]
theorem dest_eq {a b : ITree E R} (h : dest a = dest b) : a = b := by
  dsimp [dest, HpLuM.destE] at h
  exact HpLuM.ext_dest (Equiv.injective _ h)

def dtcorec
    {β : Type v}
    (gen : β →
      DeepThunk
        (MvPFunctor.uLift.{u + 1, v} (PBase E))
        (TypeVec.uLift.{u + 1, v} !![R] ::: ULift.{u + 1, v} β))
    : β → ITree E R :=
  DeepThunk.corec gen

end Sme.ITree


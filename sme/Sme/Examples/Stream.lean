import Sme.M.HpLuM

open Sme

def SS.Base : MvPFunctor 2 := ⟨
  PUnit,
  fun _ _ => PUnit
⟩

def SS.mk {α} (a : α (.fs .fz)) (b : α .fz) : SS.Base α :=
  ⟨.unit, fun | .fz, _ => b | .fs .fz, _ => a⟩

instance : EquivP (1 + 1) Prod SS.Base where
  equiv := {
    toFun x := ⟨x.2 .fz .unit, x.2 (.fs .fz) .unit⟩
    invFun p := SS.mk p.2 p.1
    left_inv :=
      fun ⟨.unit, _⟩ => Sigma.ext rfl <| heq_of_eq <| funext₂ fun | .fz, _ | .fs .fz, _ => rfl
    right_inv := fun ⟨_, _⟩ => rfl
  }

def SS α := M SS.Base !![α]

namespace SS

variable {α} (hd : α) (v : SS α)

def cons : SS α := (.mkE <| Prod.mk v hd)
def dest : α × SS α := Prod.swap v.destE

@[simp]
theorem dest_cons {α} {hd : α} {tl : SS α} : dest (cons hd tl) = ⟨hd, tl⟩ := by
  simp [cons, dest]

open scoped MvFunctor

theorem map_cons {β} {f : !![α] ⟹ !![β]}
    : f <$$> cons hd v = cons (f .fz hd) (f <$$> v) := by
  ext
  simp only [Nat.reduceAdd, M.destE, Nat.succ_eq_add_one, cons, M.mkE, TypeVec.last_eq,
    TypeVec.append1_get_fz, TypeVec.drop_append1_simp, Vec.append1.get_fz, Function.comp_apply,
    M.map_mk, M.mk_dest, Equiv.apply_symm_apply]
  apply Prod.ext <;> rfl

def take (v : SS α) : Nat → List α
  | 0 => []
  | n+1 =>
    have ⟨hd, tl⟩ := v.dest
    hd :: take tl n

end SS


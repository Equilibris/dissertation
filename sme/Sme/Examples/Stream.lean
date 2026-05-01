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

def SS α := HpLuM SS.Base (fun _ => α)

namespace SS

def cons {α} (hd : α) : SS α → SS α := (.mkE <| Prod.mk · hd)
def dest {α} (v : SS α) : α × SS α := Prod.swap v.destE

@[simp]
theorem dest_cons {α} {hd : α} {tl : SS α} : dest (cons hd tl) = ⟨hd, tl⟩ := by
  simp [cons, dest]

end SS


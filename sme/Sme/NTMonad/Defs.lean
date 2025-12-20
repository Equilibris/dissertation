import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.M.Prj
import Sme.M.HpLuM
import Sme.M.DT
import Sme.Vec

namespace Sme

def NTMonad α := HpLuM DTSum !![α]

namespace NTMonad

def dest {α} : NTMonad α → α ⊕ NTMonad α := DTSum.equiv' ∘ HpLuM.dest

def corec {α β} (f : β → α ⊕ β) : β → NTMonad α :=
  HpLuM.corec (fun v =>
    match f v with
    | .inl v => ⟨.up <| .up .true,  fun | .fs .fz, _ => .up v | .fz, h => h.down.elim⟩
    | .inr v => ⟨.up <| .up .false, fun | .fz, _ => .up v | .fs .fz, h => h.down.elim⟩)

def defer {α} : NTMonad α → NTMonad α :=
  .mk ∘ DTSum.equiv'.symm ∘ .inr

def yield {α} : α → NTMonad α :=
  .mk ∘ DTSum.equiv'.symm ∘ .inl

end Sme.NTMonad


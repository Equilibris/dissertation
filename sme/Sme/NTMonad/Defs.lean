import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.M.Prj
import Sme.M.HpLuM
import Sme.M.DT
import Sme.Vec

universe u v

namespace Sme

def NTMonad α := HpLuM DTSum !![α]

namespace NTMonad

def dest {α} : NTMonad α → α ⊕ NTMonad α := DTSum.equiv' ∘ HpLuM.dest

def corec {α β} (f : β → α ⊕ β) : β → NTMonad α :=
  HpLuM.corec (fun v =>
    match f v with
    | .inl v => ⟨.up <| .up .true,  fun | .fs .fz, _ => .up v | .fz, h => h.down.elim⟩
    | .inr v => ⟨.up <| .up .false, fun | .fz, _ => .up v | .fs .fz, h => h.down.elim⟩
  )

theorem dest_corec {α β g} (gen : β → α ⊕ β)
    : (corec gen g).dest = (gen g).map id (corec gen) := by
  dsimp [corec, dest]
  rw [HpLuM.dest_corec, ←corec]
  simp only [Nat.reduceAdd, MvQPF.comp_map]
  rw [MvFunctor.map_map, ]
  cases gen g
  <;> simp only [MvQPF.comp_map, Sum.map_inl, Sum.map_inr, id_eq]
  <;> rfl

def defer {α} : NTMonad α → NTMonad α :=
  .mk ∘ DTSum.equiv'.symm ∘ .inr

def yield {α} : α → NTMonad α :=
  .mk ∘ DTSum.equiv'.symm ∘ .inl

def dtcorec
    {α : Type u} {β : Type v}
    (gen : β →
      DeepThunk (MvPFunctor.uLift.{u, v} DTSum) (TypeVec.uLift.{u, v} !![α] ::: ULift.{u, v} β))
    : β → NTMonad α := DeepThunk.corec gen

-- An easy example of a guarded corecursion,
example : NTMonad Nat := dtcorec
  (fun (_ : Unit) => .mkE <| .inl <| .inl <| .mkE <| .inl <| .inr <| .up .unit)
  .unit

end Sme.NTMonad


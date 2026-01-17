import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
import Sme.M.HpLuM
import Sme.M.DT.Defs
import Sme.Vec
import Sme.HEq

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {α β : Type u} {n : Nat}

namespace DeepThunk

variable {P : MvPFunctor n.succ} {α : TypeVec n}

/-- `DeepThunk.corec` is a co-recursive principle allowing partially yielding results.
  It achives this by changing the recursive point to either the usual argument to the deeper call,
  or continuing the structure.
-/
def corec {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    : β → HpLuM P α :=
  .corec body ∘ gen
where
  body v := by
    -- TODO: This should just call comp.get, then transliterate
    have := comp.get v.dest
    refine ⟨
      this.fst.transliterate,
      (TypeVec.splitFun
        (fun i (h : _) => by exact ULift.transliterate <| prj.get h)
        fun h => .up ?_
      ) ⊚ this.snd ⊚ .transliterate
    ⟩
    apply DTSum.elim (fun v => prj.get v) (fun v => gen (prj.get v).down) (MvPFunctor.comp.get h)

@[simp]
theorem corec.body_fst {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β)) {w}
    : (corec.body gen w).fst = ULift.transliterate (comp.get (HpLuM.dest w)).fst :=
  rfl
@[simp]
theorem corec.body_snd {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β)) {w h}
    : (corec.body gen w).snd Fin2.fz { down := h }
    = .up (DTSum.elim
        (fun v ↦ prj.get v)
        (fun v ↦ gen (prj.get v).down)
        (comp.get ((comp.get (HpLuM.dest w)).snd Fin2.fz { down := h })))
    :=
  rfl

/- @[simp] -/
/- theorem corec.body_snd {β : Type v} -/
/-     (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β)) {w} -/
/-     : (corec.body gen w).snd =  -/
/-       (TypeVec.splitFun -/
/-         (fun i (h : _) => by exact ULift.transliterate <| prj.get h) -/
/-         fun h => .up ?_ -/
/-       ) ⊚ (comp.get v.dest).snd ⊚ TypeVec.Arrow.transliterate := by -/
/-   dsimp [corec.body] -/
/-   stop -/
/-   rfl -/

end Sme.DeepThunk


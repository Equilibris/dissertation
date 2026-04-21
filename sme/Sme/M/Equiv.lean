import Sme.ABI
import Sme.M.SM
import Sme.PFunctor.Utils
import Mathlib.Logic.Small.Defs

open scoped MvFunctor
open MvPFunctor

namespace Sme.SM

universe u v w

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n}

def equivP : SM.{u, max u v} P α ≃ M.{u} P α :=
  let msm := (MvFunctor.map (TypeVec.id ::: ULift.up.{u, max u v + 1}) ∘ SM.dest)
  let mpa := liftAppend.{u, max u v} ∘ M.dest P ∘ ULift.down.{max u v, u}
  ⟨
    .corecU P msm,
    .corec mpa ∘ ULift.up,
    fun x => SM.bisim ⟨
      (· = (.corec mpa ∘ ULift.up ∘ .corecU _ msm) ·),
      by
        rintro _ ⟨⟨gen, g⟩⟩ rfl
        dsimp
        exact (MvPFunctor.liftR_iff _ _ _).mpr ⟨
          .up (gen g).fst.down,
          fun
            | .fz, h => .corec mpa
              <| ULift.up
              <| M.corecU P msm
              <| corec gen (((gen g).snd Fin2.fz ∘ ULift.up) h.down).down
            | .fs s, .up h => (gen g).snd (.fs s) (.up h) |>.down |> .up,
          fun
            | .fz, h  => .corec gen ((gen g).snd .fz (.up h.down)).down
            | .fs s, h => (gen g).snd (.fs s) (.up h.down) |>.down |> .up,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          fun | .fz, h | .fs _, h => rfl,
        ⟩,
      rfl
    ⟩,
    fun x => M.bisim _
      (· = (.corecU _ msm ∘ .corec mpa ∘ .up) ·)
      (fun a b => (· ▸ ⟨
        (corec mpa <| .up b).dest.fst.down,
        ((M.dest P b).snd ·.fs),
        (M.corecU P msm <| (corec mpa <| .up b).dest.snd Fin2.fz <|.up ·),
        (M.dest P b).snd .fz,
        Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
        Sigma.ext rfl <| .refl _,
        fun _ => rfl
      ⟩))
      _ _
      rfl,
  ⟩

/-- info: 'Sme.SM.equivP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equivP

end Sme.SM

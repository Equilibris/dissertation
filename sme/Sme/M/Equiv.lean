import Sme.ABI
import Sme.M.SM
import Sme.M.Utils
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
      fun a b => by
        rcases b with ⟨⟨gen, g⟩⟩
        rintro rfl
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
        Sigma.ext rfl <| heq_of_eq rfl,
        fun _ => rfl
      ⟩))
      _ _
      rfl,
  ⟩

section

@[pp_with_univ]
def equivXU : SM.{u, max u v} P α ≃ SM.{u, max u w} P α :=
  equivP.trans equivP.symm

namespace equivXU 

theorem inv'
    {x : SM.{u, max u v} P α}
    : SM.equivXU x = x := by
  simp [SM.equivXU]

theorem contract'
    {x : SM.{u, max u v} P α}
    : (equivXU ∘ equivXU) x = equivXU x := by
  simp [equivXU]

theorem toFun_invFun'
    {x : SM.{u, max u v} P α}
    : equivXU x = equivXU.symm x := by
  simp [equivXU]

def transform
    (v : (MvPFunctor.uLift.{u, (max u w) + 1} P)
      (TypeVec.uLift.{u, (max u w) + 1} α ::: SM.{u, max u w} P α))
    : (MvPFunctor.uLift.{u, (max u v) + 1} P) 
      (TypeVec.uLift.{u, (max u v) + 1} α ::: SM.{u, max u v} P α) :=
  ⟨
    .up v.fst.down,
    fun
      | .fz, h => equivXU (v.snd .fz (.up h.down))
      | .fs s, h => .up (v.snd (s.fs) (.up h.down)).down
  ⟩

end equivXU

@[simp]
theorem transform_dest
    {x : SM.{u, max u v} P α}
    : (equivXU.{u, v, w} x).dest = equivXU.transform (dest x) := by
  dsimp [equivXU, equivP]
  simp [dest_corec]
  refine Sigma.ext (by rfl) <| heq_of_eq ?_
  funext i h
  rcases i with (_|⟨s⟩)
  · rfl
  · rfl

-- The soundness of this is extremely dubious
private unsafe def equivXUImpl : SM.{u, max u v} P α ≃ SM.{u, max u w} P α where
  toFun := unsafeCast
  invFun := unsafeCast
  left_inv _ := lcProof
  right_inv _ := lcProof

attribute [irreducible, implemented_by equivXUImpl] equivXU

end

/-- info: 'Sme.SM.equivP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equivP

end Sme.SM

import Sme.M.SDefs
import Sme.ABI
import Sme.M.Utils
import Mathlib.Logic.Small.Defs

open MvPFunctor

namespace Sme

universe u v w

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n}

def SM.equivP : SM.{u, max u v} P α ≃ M.{u} P α :=
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
def SM.equivXU : SM.{u, max u v} P α ≃ SM.{u, max u w} P α :=
  SM.equivP.trans SM.equivP.symm

theorem SM.equivXU.inv'
    {x : SM.{u, max u v} P α}
    : SM.equivXU x = x := by
  simp [SM.equivXU]

theorem SM.equivXU.contract'
    {x : SM.{u, max u v} P α}
    : (SM.equivXU ∘ SM.equivXU) x = SM.equivXU x := by
  simp [SM.equivXU]

theorem SM.equivXU.toFun_invFun'
    {x : SM.{u, max u v} P α}
    : SM.equivXU x = SM.equivXU.symm x := by
  simp [SM.equivXU]

def SM.equivXU.transform
    (v : (MvPFunctor.uLift.{u, (max u w) + 1} P)
      (TypeVec.uLift.{u, (max u w) + 1} α ::: SM.{u, max u w} P α))
    : (MvPFunctor.uLift.{u, (max u v) + 1} P) 
      (TypeVec.uLift.{u, (max u v) + 1} α ::: SM.{u, max u v} P α) :=
  ⟨
    .up v.fst.down,
    fun
      | .fz, h => SM.equivXU (v.snd .fz (.up h.down))
      | .fs s, h => .up (v.snd (s.fs) (.up h.down)).down
  ⟩

theorem SM.v
    {x : SM.{u, max u v} P α}
    : (SM.equivXU.{u, v, w} x).dest = SM.equivXU.transform (SM.dest x) := by
  dsimp [equivXU, equivP]
  simp [SM.dest_corec]
  refine Sigma.ext (by rfl) <| heq_of_eq ?_
  funext i h
  rcases i with (_|⟨s⟩)
  · rfl
  · rfl

-- The soundness of this is extremely dubious
private unsafe def SM.equivXUImpl : SM.{u, max u v} P α ≃ SM.{u, max u w} P α where
  toFun := unsafeCast
  invFun := unsafeCast
  left_inv _ := lcProof
  right_inv _ := lcProof

attribute [irreducible, implemented_by SM.equivXUImpl] SM.equivXU

end

/-- info: 'Sme.SM.equivP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SM.equivP

def HpLuM (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) : Type u :=
  ABI _ _ (SM.equivP.{u, u} (P := P) (α := α)).symm

section HpLuM

def corec
    {β : Type v}
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : HpLuM P α :=
  have := SM.corec gen g
  .mkB sorry

#check SM.dest
set_option pp.universes true in
def dest : HpLuM P α → P (α ::: HpLuM P α) := sorry

end HpLuM

end Sme

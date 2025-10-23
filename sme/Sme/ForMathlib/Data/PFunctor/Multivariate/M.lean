import Mathlib.Data.PFunctor.Multivariate.M
import Mathlib.Tactic.DepRewrite
import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic

universe u v

open MvFunctor TypeVec

namespace MvPFunctor

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

theorem congr_heq' {α₁ α₂ β₁ β₂ : Sort _} {f : α₁ → β₁} {g : α₂ → β₂} {x : α₁} {y : α₂}
    (h₀ : β₁ = β₂) (h₁ : f ≍ g) (h₂ : x ≍ y) : f x ≍ g y := by
  cases h₀; exact heq_of_eq <| congr_heq h₁ h₂

def M.corecU
    {α : TypeVec.{u} n} {β : Type v}
    (gen : β → P.uLift (α.uLift.append1 <| ULift.{u, v} β))
    : β → P.M α :=
  M.corec' P
    (gen · |>.fst.down)
    (gen · |>.snd |> dropFun |>.uLift_arrow)
    (fun x => (.up · |> (gen x |>.snd |> lastFun) |>.down))

def genU {P : _} {α : TypeVec.{u} n} {β : Type u} (gen : β → P (α.append1 β))
    : β → uLift P (TypeVec.uLift α ::: ULift β) :=
  /- (uLift_append1_ULift_uLift.symm ▸ uLift_up.{u, u} P <| gen ·) -/
  (cast (congr rfl uLift_append1_ULift_uLift.symm) <| uLift_up.{u, u} <| gen ·)

theorem genU.fst {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {β : Type u}
    (g : β → P (α ::: β)) (x : β)
    : (genU g x).fst.down = (g x).fst := by
  apply eq_of_heq
  apply HEq.trans (b := (P.uLift_up (g x)).fst.down)
  · congr!
    · exact uLift_append1_ULift_uLift
    · apply cast_heq
  · rfl

theorem genU.snd {n : ℕ} (P : MvPFunctor.{u} (n + 1)) {α : TypeVec.{u} n} {β : Type u}
    (g : β → P (α ::: β)) (x : β) : (genU g x).snd ≍ (P.uLift_up (g x)).snd := by
  apply dcongr_heq (cast_heq _ (uLift_up (g x)))
  · congr!
    <;> rw [uLift_append1_ULift_uLift]
  · intro heq
    congr!
    rw [uLift_append1_ULift_uLift]

theorem M.dest_corecU {α : TypeVec n} {β : Type v}
    (g : β → P.uLift (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (x : β) :
    M.dest P (M.corecU P g x) =
      (P.uLift_down <|
      (Arrow.uLift_up ⊚ (Arrow.uLift_down ::: (M.corecU P g ·.down))) <$$> g x) := by
  trans
  · apply M.dest_corec'
  dsimp only
  rw [←Sigma.eta (g x)]
  dsimp only
  rw [MvPFunctor.map_eq]
  congr 1
  change splitFun _ (_ ∘ (ULift.down ∘ lastFun (g x).snd ∘ ULift.up)) = _
  conv =>
    lhs; rhs; lhs; rhs
    change fun x ↦ ULift.down ∘ (lastFun (g x).snd) ∘ ULift.up
  conv_rhs => rw [← split_dropFun_lastFun (g x).snd]
  rw [Arrow.uLift_up_splitFun, comp_assoc,
    appendFun_comp_splitFun,
    ← splitFun_comp, ←comp_assoc,
    Arrow.uLift_up_down, id_comp]
  dsimp
  rw [Arrow.uLift_arrow_splitFun]
  rfl

theorem M.dest_corecU_gen_fn {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) (x : β) :
    M.dest P (M.corecU P (genU g) x) = appendFun id (M.corecU P (genU g)) <$$> g x := by
  trans
  · exact M.dest_corecU (α := α) P (genU g) x
  change P.uLift_down
    ((Arrow.uLift_up ⊚ (Arrow.uLift_down ::: (corecU P (genU g) ∘ ULift.down))) <$$> genU g x) = _
  unfold uLift_down
  rw [←Sigma.eta (g x)]
  have gen_fst := genU.fst P g x
  have gen_snd := genU.snd P g x
  congr 1
  · apply Function.hfunext rfl
    rintro a b r
    subst r
    cases a
    · change corecU _ _ ∘ ULift.down ∘ ((genU g x).snd .fz) ∘ ULift.up ≍ corecU _ _ ∘ _
      congr! 2
      apply Function.hfunext ‹_›
      intro a b heq
      obtain rfl : a = cast (by rw [gen_fst]) b := eq_cast_iff_heq.mpr heq
      clear heq
      dsimp [genU]
      apply HEq.trans (b := (((P.uLift_up (g x))).snd Fin2.fz { down := b }).down)
      case h₂ => rfl
      congr!
      apply eq_of_heq
      refine congr_heq' rfl ?_ ?arg
      case arg =>
        congr! 1
        apply cast_heq
      apply dcongr_heq (.refl _)
      · intro _ _ heq
        obtain rfl := eq_of_heq heq
        conv =>
          lhs; lhs; lhs
          change (genU g x).fst
        conv =>
          rhs; lhs; lhs
          dsimp [uLift_up]
          rw [←gen_fst]
          change (genU g x).fst
        congr!
        rw [uLift_append1_ULift_uLift]
      intro _ _
      exact gen_snd
    case fs a =>
      change ULift.down ∘ (genU g x).snd a.fs ∘ ULift.up ≍ (g x).snd a.fs
      apply HEq.trans (b := (ULift.down ∘ (((g x).snd.arrow_uLift)) a.fs ∘ ULift.up))
      case h₂ => rfl
      apply Function.hfunext
      · exact congrFun (congrArg P.B gen_fst) a.fs
      intro a b heq
      change ULift.down _ ≍ ULift.down _
      congr!
      dsimp
      apply congr_heq
      case h₂ => congr!
      apply dcongr_heq (heq_of_eq rfl)
      · intro a b h
        obtain rfl := eq_of_heq h
        rw [←gen_fst]
        cases a <;> rfl
      congr!

theorem M.corec_corecU
    {P : MvPFunctor.{u} (n + 1)}
    {α : TypeVec.{u} n}
    {β : Type u}
    {gen : β → P (α.append1 β)}
  : corec P gen = corecU P (genU gen) := funext fun b => by
    dsimp [corec, corecU]
    congr
    · funext g
      exact (genU.fst P gen g).symm
    · apply Function.hfunext rfl
      intro a _ .rfl
      sorry
    · sorry

end MvPFunctor


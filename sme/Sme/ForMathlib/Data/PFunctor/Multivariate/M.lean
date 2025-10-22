import Mathlib.Data.PFunctor.Multivariate.M
import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic

universe u v

open MvFunctor TypeVec

namespace MvPFunctor

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

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

end MvPFunctor


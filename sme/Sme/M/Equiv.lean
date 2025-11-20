import Sme.M.SDefs

open MvPFunctor

namespace Sme

universe u v

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n}

def liftAppend {β} (v : P (α ::: β))
    : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α ::: ULift β) :=
  ⟨.up v.fst, fun
    | .fz, h => .up (v.snd .fz h.down)
    | .fs s, h => .up (v.snd s.fs h.down)⟩

/- set_option pp.universes true in -/
def SM.equiv : SM.{u, u} P α ≃ M.{u} P α := ⟨
  M.corecU P (MvFunctor.map (TypeVec.id ::: ULift.up.{u, u+1}) ∘ SM.dest),
  SM.corec (liftAppend ∘ M.dest P),
  fun x => SM.bisim ⟨
    fun a b => a = .corec
        (liftAppend ∘ M.dest P)
        (.corecU _ (MvFunctor.map (TypeVec.id ::: ULift.up.{u, u+1}) ∘ SM.dest) b),
    fun a b => by
      induction b using Quotient.ind; rename_i b
      rcases b with ⟨gen, g⟩
      rintro rfl
      apply (MvPFunctor.liftR_iff _ _ _).mpr
      refine ⟨
        .up (gen g).fst.down,
        fun
          | .fz, h  => .corec (liftAppend ∘ M.dest P)
            <| M.corecU P (MvFunctor.map (TypeVec.id ::: ULift.up.{u, u+1}) ∘ SM.dest)
            <| corec gen (((gen g).snd Fin2.fz ∘ ULift.up) h.down).down
          | .fs s, .up h => (gen g).snd (.fs s) (.up h) |>.down |> .up,
        ?f1,
        ?e0,
        ?e1,
        ?h
      ⟩
      case e0 =>
        rw [dest_corec]
        unfold Function.comp
        apply Sigma.ext
        · rfl
        apply heq_of_eq
        funext i h
        rcases h with ⟨h⟩
        rcases i with (_|_)
        · rfl
        · rfl
      · exact fun
          | .fz, h  => .corec gen ((gen g).snd .fz (.up h.down)).down
          | .fs s, h => (gen g).snd (.fs s) (.up h.down) |>.down |> .up
      · refine Sigma.ext rfl <| heq_of_eq ?_
        funext i h
        rcases h with ⟨h⟩
        rcases i with (_|_)
        · rfl
        · rfl
      case h =>
        rintro (_|i) ⟨h⟩
        · simp [TypeVec.RelLast]
        · rfl
      ,
    rfl
  ⟩,
  fun x => M.bisim _
    (fun a b => a = .corecU _ (MvFunctor.map (TypeVec.id ::: ULift.up.{u, u+1}) ∘ SM.dest)
      (.corec (liftAppend ∘ M.dest _) b))
    (fun a b => by
      rintro rfl
      rw [M.dest_corecU]
      use (corec (liftAppend ∘ M.dest P) b).dest.fst.down
      use fun i h => (M.dest P b).snd i.fs h
      use fun h => by 
        apply M.corecU P (MvFunctor.map (TypeVec.id ::: ULift.up.{u, u+1}) ∘ SM.dest)
        exact ((corec (liftAppend ∘ M.dest P) b).dest.snd Fin2.fz { down := h })
      use fun h => (M.dest P b).snd .fz h
      refine ⟨?_, ?_, ?_⟩
      · refine Sigma.ext rfl <| heq_of_eq <| funext fun | .fz => rfl | .fs _ => rfl
      · refine Sigma.ext rfl <| heq_of_eq rfl
      · exact fun _ => rfl
      )
    _ _
    rfl,
⟩

/-- info: 'Sme.SM.equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SM.equiv 

end Sme

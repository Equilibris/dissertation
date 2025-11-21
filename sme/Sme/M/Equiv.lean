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

def SM.equiv : SM.{u, u} P α ≃ M.{u} P α :=
  let lifter := (TypeVec.id ::: ULift.up.{u, u+1})
  ⟨
    M.corecU P (MvFunctor.map lifter ∘ SM.dest),
    SM.corec (liftAppend ∘ M.dest P),
    fun x => SM.bisim ⟨
      fun a b => a = .corec
          (liftAppend ∘ M.dest P)
          (.corecU _ (MvFunctor.map lifter ∘ SM.dest) b),
      fun a b => by
        induction b using Quotient.ind; rename_i b
        rcases b with ⟨gen, g⟩
        rintro rfl
        rw [dest_corec]
        exact (MvPFunctor.liftR_iff _ _ _).mpr ⟨
          .up (gen g).fst.down,
          fun
            | .fz, h  => .corec (liftAppend ∘ M.dest P)
              <| M.corecU P (MvFunctor.map lifter ∘ SM.dest)
              <| corec gen (((gen g).snd Fin2.fz ∘ ULift.up) h.down).down
            | .fs s, .up h => (gen g).snd (.fs s) (.up h) |>.down |> .up,
          fun
            | .fz, h  => .corec gen ((gen g).snd .fz (.up h.down)).down
            | .fs s, h => (gen g).snd (.fs s) (.up h.down) |>.down |> .up,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          fun | .fz, h | .fs _, h => rfl
        ⟩,
      rfl
    ⟩,
    fun x => M.bisim _
      (fun a b => a = .corecU _ (MvFunctor.map (TypeVec.id ::: ULift.up.{u, u+1}) ∘ SM.dest)
        (.corec (liftAppend ∘ M.dest _) b))
      (fun a b => by
        rintro rfl
        exact ⟨
          (corec (liftAppend ∘ M.dest P) b).dest.fst.down,
          ((M.dest P b).snd ·.fs),
          (M.corecU P
            (MvFunctor.map (TypeVec.id ::: ULift.up.{u, u+1}) ∘ SM.dest)
            <| (corec (liftAppend ∘ M.dest P) b).dest.snd Fin2.fz <|.up ·),
          (M.dest P b).snd .fz,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          Sigma.ext rfl <| heq_of_eq rfl,
          fun _ => rfl
        ⟩
      )
      _ _
      rfl,
  ⟩

/-- info: 'Sme.SM.equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SM.equiv

def liftAppend' {β} (v : P (α ::: β))
    : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α ::: ULift.{u, max u v} (ULift β)) :=
  ⟨.up v.fst, fun
    | .fz, h => .up <| .up (v.snd .fz h.down)
    | .fs s, h => .up (v.snd s.fs h.down)⟩

def SM.equivP : SM.{u, max u v} P α ≃ M.{u} P α :=
  let lifter := (TypeVec.id ::: ULift.up.{u, max u v + 1})
  let m := (liftAppend'.{u, max u v} ∘ M.dest P ∘ ULift.down.{max u v, u})
  ⟨
    .corecU P (MvFunctor.map lifter ∘ SM.dest),
    .corec m ∘ ULift.up.{max u v, u},
    fun x => SM.bisim ⟨
      fun a b => a =
        (.corec m ∘ ULift.up.{max u v, u})
         (.corecU _ (MvFunctor.map lifter ∘ SM.dest) b),
      fun a b => by
        induction b using Quotient.ind; rename_i b
        rcases b with ⟨gen, g⟩
        rintro rfl
        exact (MvPFunctor.liftR_iff _ _ _).mpr ⟨
          .up (gen g).fst.down,
          fun
            | .fz, h  => .corec m
              <| ULift.up
              <| M.corecU P (MvFunctor.map lifter ∘ SM.dest)
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
      (fun a b => a = .corecU _ (MvFunctor.map lifter ∘ SM.dest) (.corec m <|.up b))
      (fun a b => by
        rintro rfl
        exact ⟨
          (corec m <| .up b).dest.fst.down,
          ((M.dest P b).snd ·.fs),
          (M.corecU P
            (MvFunctor.map lifter ∘ SM.dest)
            <| (corec m <| .up b).dest.snd Fin2.fz <|.up ·),
          (M.dest P b).snd .fz,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          Sigma.ext rfl <| heq_of_eq rfl,
          fun _ => rfl
        ⟩
      )
      _ _
      rfl,
  ⟩

/-- info: 'Sme.SM.equivP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SM.equivP 

end Sme

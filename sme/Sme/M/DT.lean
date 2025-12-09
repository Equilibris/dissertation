import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.M.Prj
import Sme.M.HpLuM
import Sme.Vec

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v

inductive DTSum (α β : Type u) : Type u
  /-- Hand responsibility back to the co-recursor -/
  | recall (v : α)
  /-- Continue constructing a DeepThunk -/
  | cont   (v : β)

variable {α β : Type u} {n : Nat}

namespace DTSum

def equivSum : DTSum α β ≃ α ⊕ β where
  toFun
    | .recall a => .inl a
    | .cont   a => .inr a
  invFun
    | .inl a => .recall a
    | .inr a => .cont a

  left_inv  := fun | .recall _ | .cont _ => rfl
  right_inv := fun | .inl _ | .inr _ => rfl

def Uncurried : MvPFunctor 2 where
  A := ULift Bool
  B := fun
    | .up .true   => !![PUnit, PEmpty]
    | .up .false  => !![PEmpty, PUnit]

def equiv {α : TypeVec 2} : Uncurried α ≃ DTSum (α <| .fs .fz) (α <| .fz) where
  toFun := fun
    | ⟨.up .true,  v⟩ => .recall (v (.fs .fz) .unit)
    | ⟨.up .false, v⟩ => .cont (v (.fz) .unit)
  invFun := fun
    | .recall v => ⟨.up .true, fun | .fz, e => e.elim | .fs .fz, .unit => v⟩
    | .cont v => ⟨.up .false, fun | .fs .fz, e => e.elim | .fz, .unit => v⟩
  left_inv := by
    rintro (_|_)
    <;> refine Sigma.ext rfl <| heq_of_eq ?_
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> cases h
    <;> simp
  right_inv := fun | .recall _ | .cont _ => rfl

end DTSum

namespace DeepThunk

abbrev innerMapper {n} : Vec (MvPFunctor (n.succ)) n
  | .fz => comp DTSum.Uncurried !![prj <| .fs .fz, prj .fz]
  | .fs n => prj (n.add 2)

abbrev HoFunctor {n} (F : MvPFunctor n) : MvPFunctor (n + 1) := comp F innerMapper

/-- Between the original functor and the ⊕-composed functor there is an injection,
    it occurs by taking the right step at every point co-recursively.

    The instances of the hof will have this defined as a coercion. -/
def inject
  {P : MvPFunctor n.succ} {α : TypeVec n} : HpLuM P α → HpLuM (HoFunctor P) (α ::: β) :=
  .corec' fun v =>  by
    refine comp.mk <|
      (TypeVec.splitFun
        ?_
        ?_
      ) <$$> v.dest
    · exact (fun i h => prj.mk (i.add 2) h)
    exact fun h => comp.mk ⟨
      .up .false,
      TypeVec.splitFun
        (TypeVec.splitFun TypeVec.nilFun PEmpty.elim) 
        fun _ => ⟨.unit, (TypeVec.repeat_out fun _ => PEmpty.elim) ::: fun _ => h⟩
      ⟩
/-- `DeepThunk.corec` is a co-recursive principle allowing partially yielding results.
  It achives this by changing the recursive point to either the usual argument to the deeper call,
  or continuing the structure.
-/
def corec
    {β : Type v}
    {P : MvPFunctor n.succ} {α : TypeVec.{u} n}
    (gen : β → HpLuM (HoFunctor <| uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    : β → HpLuM P α
    :=
  .corec (fun (v : HpLuM _ _) => by
      refine ⟨(comp.get v.dest).fst.transliterate, ?_⟩
      refine (TypeVec.splitFun
        (fun i h => ULift.transliterate ?_)
        fun h => .up ?_
      ) ⊚ (comp.get v.dest).snd ⊚ TypeVec.Arrow.transliterate
      · exact (h.snd (i.add 2)) (prj.fn_same.mpr .unit)
      exact match DTSum.equiv <| MvPFunctor.comp.get h with
        | .recall v => gen <| ULift.down (v.snd (.fs .fz) .unit)
        | .cont v => (v.snd .fz .unit)
    ) ∘ gen

theorem corec.eq 
    {β : Type v}
    {P : MvPFunctor n.succ} {α : TypeVec.{u} n}
    (gen : β → HpLuM (HoFunctor <| uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    {g : β}
    : (corec gen g).dest = uLift_down sorry := by
  have : HpLuM
      (HoFunctor (uLift.{u, v} P)) 
      (TypeVec.uLift.{u, v} α ::: ULift.{max u v, u} (HpLuM P α)) := 
    (gen g).map (TypeVec.id ::: ULift.up ∘ sorry ∘ ULift.down)
  dsimp [corec]
  rw [HpLuM.dest_corec]
  sorry

end DeepThunk

end Sme

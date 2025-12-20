import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.M.Prj
import Sme.M.HpLuM
import Sme.Vec
import Sme.EquivP

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v

variable {α β : Type u} {n : Nat}

def DTSum : MvPFunctor 2 where
  A := ULift Bool
  B := fun
    | .up .true   => !![PUnit, PEmpty]
    | .up .false  => !![PEmpty, PUnit]

instance : EquivP 2 Sum DTSum where
  equiv := {
    toFun
      | ⟨.up .true, v⟩ => .inr (v (.fs .fz) .unit)
      | ⟨.up .false, v⟩ => .inl (v .fz .unit)
    invFun
      | .inl v => ⟨.up .false, fun | .fs .fz, h => h.elim | .fz, h => v⟩
      | .inr v => ⟨.up .true,  fun | .fs .fz, h => v | .fz, h => h.elim⟩
    right_inv
      | .inl _ | .inr _ => rfl
    left_inv := by
      rintro ⟨(_|_), h⟩
      <;> refine Sigma.ext rfl <| heq_of_eq ?_
      <;> funext i h
      <;> rcases i with (_|_|_|_)
      <;> cases h
      <;> rfl
  }

namespace DTSum

def cont {α} (v : α .fz) : DTSum α :=
  ⟨.up .false, fun | .fs .fz, e => e.elim | .fz, .unit => v⟩

def recall {α} (v : α <| .fs .fz) : DTSum α :=
  ⟨.up .true,  fun | .fz, e => e.elim | .fs .fz, .unit => v⟩

def equiv {α : TypeVec 2} : DTSum α ≃ (α <| .fs .fz) ⊕ (α <| .fz) where
  toFun := fun
    | ⟨.up .true,  v⟩ => .inl (v (.fs .fz) .unit)
    | ⟨.up .false, v⟩ => .inr (v (.fz) .unit)
  invFun := fun
    | .inl v => recall v
    | .inr v => cont v
  left_inv := by
    rintro (_|_)
    <;> refine Sigma.ext rfl <| heq_of_eq ?_
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> cases h
    <;> simp [cont, recall]
  right_inv := fun | .inl _ | .inr _ => rfl

def equiv' {α β} : DTSum !![α, β] ≃ α ⊕ β where
  toFun := fun
    | ⟨.up .true,  v⟩ => .inl (v (.fs .fz) .unit)
    | ⟨.up .false, v⟩ => .inr (v (.fz) .unit)
  invFun := fun
    | .inl v => recall v
    | .inr v => cont v
  left_inv := by
    rintro (_|_)
    <;> refine Sigma.ext rfl <| heq_of_eq ?_
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> cases h
    <;> simp [cont, recall]
  right_inv := fun | .inl _ | .inr _ => rfl

end DTSum

abbrev DeepThunk.innerMapper {n} : Vec (MvPFunctor (n.succ)) n
  | .fz => comp DTSum !![prj <| .fs .fz, prj .fz]
  | .fs n => prj (n.add 2)

-- Takes a functor P α β γ ⋯, and maps it to P (ξ ⊕ α) β γ ⋯
abbrev DeepThunk.NatTrans {n} (P : MvPFunctor n) : MvPFunctor (n + 1) := comp P innerMapper

def DeepThunk {n} (P : MvPFunctor n) := HpLuM (DeepThunk.NatTrans P)

namespace DeepThunk

-- TODO: Change this to use ⊕ instead of DTSum
def DTComp (F : CurriedTypeFun.{u, v} n) : CurriedTypeFun.{u, v} n.succ :=
  CurriedTypeFun.append fun ξ =>
    .ofTvF fun α =>
      sorry
    /- F (innerMapper · α) -/

instance {n} {F : CurriedTypeFun.{u, v} n} {P} [efp : EquivP _ F P]
    : EquivP _ (DTComp F) (NatTrans P) where
  equiv := {
    toFun v := efp.equiv <| comp.get v
    invFun v := comp.mk sorry
    left_inv := sorry
    right_inv := sorry
  }

/-- Between the original functor and the ⊕-composed functor there is an injection,
    it occurs by taking the right step at every point co-recursively.

    The instances of the hof will have this defined as a coercion. -/
def inject
  {P : MvPFunctor n.succ} {α : TypeVec n} : HpLuM P α → DeepThunk P (α ::: β) :=
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
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    : β → HpLuM P α :=
  .corec (fun (v : HpLuM _ _) => by
      refine ⟨(comp.get v.dest).fst.transliterate, ?_⟩
      refine (TypeVec.splitFun
        (fun i h => ULift.transliterate ?_)
        fun h => .up ?_
      ) ⊚ (comp.get v.dest).snd ⊚ TypeVec.Arrow.transliterate
      · exact h.snd (i.add 2) (prj.fn_same.mpr .unit)
      exact match DTSum.equiv <| MvPFunctor.comp.get h with
        | .inl v => gen <| ULift.down (v.snd (.fs .fz) .unit)
        | .inr v => (v.snd .fz .unit)
    ) ∘ gen

end DeepThunk

end Sme

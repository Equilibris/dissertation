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

universe u v w

variable {α β : Type u} {n : Nat}

def DTSum : MvPFunctor 2 where
  A := ULift Bool
  B := fun
    | .up .true   => !![PUnit, PEmpty]
    | .up .false  => !![PEmpty, PUnit]

instance DTSum.eqSum : EquivP 2 Sum DTSum where
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
      <;> rcases h with (_|_)
      <;> rfl
  }

-- TODO: Is this some categorical object
instance DTSum.uEqSum : EquivP 2 Sum DTSum.uLift where
  equiv := {
    toFun
      | ⟨.up <| .up .true, v⟩ => .inr (v (.fs .fz) (.up .unit))
      | ⟨.up <| .up .false, v⟩ => .inl (v .fz (.up .unit))
    invFun
      | .inl v => ⟨.up <| .up .false, fun | .fs .fz, h => h.down.elim | .fz, h => v⟩
      | .inr v => ⟨.up <| .up .true,  fun | .fs .fz, h => v | .fz, h => h.down.elim⟩
    right_inv
      | .inl _ | .inr _ => rfl
    left_inv := by
      rintro ⟨(_|_), h⟩
      <;> refine Sigma.ext rfl <| heq_of_eq ?_
      <;> funext i h
      <;> rcases i with (_|_|_|_)
      <;> rcases h with (_|_)
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

def lift (α : TypeVec.{max v u} 2) : uLift.{u, v} DTSum α ≃ DTSum α := calc
  _ ≃ _ := uEqSum.equiv
  _ ≃ _ := eqSum.equiv.symm

end DTSum

namespace DeepThunk
abbrev innerMapper {n} : Vec (MvPFunctor n.succ) n
  | .fz => .comp DTSum !![.prj <| .fs .fz, .prj .fz]
  | .fs n => .prj (n.add 2)

abbrev innerMapperC {n} : Vec (CurriedTypeFun n.succ) n
  | .fz => .comp (show CurriedTypeFun 2 from Sum) !![.prj <| .fs .fz, .prj .fz]
  | .fs n => .prj (n.add 2)

instance {n} : {i : Fin2 n} → EquivP _ (innerMapperC i) (innerMapper i)
  | .fz => by
    apply EquivP.comp' inferInstance
    rintro (_|_|_|_)
    <;> dsimp
    <;> infer_instance
  | .fs _ => by dsimp [innerMapperC, innerMapper]; infer_instance

-- Takes a functor P α β γ ⋯, and maps it to P (ξ ⊕ α) β γ ⋯
abbrev NatTrans {n} (P : MvPFunctor n) : MvPFunctor (n + 1) := .comp P innerMapper
end DeepThunk

def DeepThunk {n} (P : MvPFunctor n) := HpLuM (DeepThunk.NatTrans P)

namespace DeepThunk

-- TODO: Change this to use ⊕ instead of DTSum
def DTComp (F : CurriedTypeFun.{u, v} n) : CurriedTypeFun.{u, v} n.succ :=
  .comp F innerMapperC

instance (priority := 100) {n} {F : CurriedTypeFun.{u, v} n} {P} [efp : EquivP _ F P]
    : EquivP _ (DTComp F) (NatTrans P) := by
  dsimp [DTComp]
  infer_instance

variable {P : MvPFunctor n.succ} {α : TypeVec n}

/-- Between the original functor and the ⊕-composed functor there is an injection,
    it occurs by taking the right step at every point co-recursively.

    The instances of the hof will have this defined as a coercion. -/
def inject : HpLuM P α → DeepThunk P (α ::: β) :=
  .corec' fun v =>  by
    refine comp.mk <|
      (TypeVec.splitFun
        ?_
        ?_
      ) <$$> v.dest
    · exact (fun i h => prj.mk (i.add 2) h)
    exact fun h => comp.mk ⟨
      .up .false,
      TypeVec.splitFun (TypeVec.splitFun TypeVec.nilFun PEmpty.elim)
        fun _ => ⟨.unit, (TypeVec.repeat_out fun _ => PEmpty.elim) ::: fun _ => h⟩
    ⟩

theorem dest_inject {x : HpLuM P α}
    : (inject x : DeepThunk P (α ::: β)).dest
    = comp.mk (TypeVec.splitFun
      (fun (i : Fin2 n) v => (by apply prj.mk (i.add 2) v))
      (fun v => by exact comp.mk ⟨
        .up .false,
        TypeVec.splitFun
          (fun | .fz, h => h.elim)
          (fun _ => prj.mk Fin2.fz <| inject v)⟩
      ) <$$> x.dest) := by
  rw [inject, HpLuM.dest_corec', ←inject, comp.map_mk]
  simp only [Nat.succ_eq_add_one, Vec.append1.get_fz, MvFunctor.map_map, TypeVec.splitFun_comp']
  unfold Function.comp TypeVec.comp
  simp only
  conv =>
    lhs; arg 1; lhs; lhs; intro i x
    rw [prj.map_mk]
    change prj.mk i.fs.fs x
  congr
  funext v
  rw [comp.map_mk]
  change comp.mk ⟨_, _⟩ = _
  rw [TypeVec.splitFun_comp']
  congr 3
  · simp only [Vec.append1.get_fs]
    funext i x
    rcases i with (_|_|_)
    simp only [TypeVec.comp.get, Vec.append1.get_fz, TypeVec.splitFun.get_fz, Function.comp_apply]
    exact x.elim
  · funext i
    change _ <$$> prj.mk _ _ = _
    rw [prj.map_mk]
    rfl
  /- sorry -/

theorem inject.injection : Function.Injective (inject : HpLuM P α → DeepThunk P (α ::: β)) := by
  intro a b h
  apply HpLuM.bisim (inject · = inject ·) h
  intro a b h
  have h0 := HpLuM.ext_dest_iff.mp h
  rw [dest_inject, dest_inject] at h0
  have h1 := comp.mk_bij.injective h0; clear h0
  have : a.dest.fst = b.dest.fst := by
    sorry
  stop
  simp [MvFunctor.map_map, TypeVec.splitFun_comp'] at h1
  unfold Function.comp TypeVec.comp at h1
  simp at h1
  conv at h1 =>
    lhs; lhs; lhs; intro i x
    rw [prj.map_mk (by dsimp [Fin2.add]) (by funext _; simp [Fin2.add, TypeVec.id]), cast_eq]
  conv at h1 =>
    rhs; lhs; lhs; intro i x
    rw [prj.map_mk (by dsimp [Fin2.add]) (by funext _; simp [Fin2.add, TypeVec.id]), cast_eq]
  conv at h1 =>
    lhs; lhs; rhs; intro x
    rw [comp.map_mk]
    change comp.mk ⟨.up .false, _⟩
    rw [TypeVec.splitFun_comp']
    unfold Function.comp TypeVec.comp
    simp []
    arg 1; arg 2; lhs; intro i x
  sorry


instance : Coe (HpLuM P α) (DeepThunk P (α ::: β)) := ⟨inject⟩

/-- `DeepThunk.corec` is a co-recursive principle allowing partially yielding results.
  It achives this by changing the recursive point to either the usual argument to the deeper call,
  or continuing the structure.
-/
def corec {β : Type v}
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

theorem inject_corec {x : HpLuM (P.uLift) α} {v : β}
    : corec (fun _ => inject x.uLift_up) v = x := sorry

def bind {β γ : Type v} {α : TypeVec.{u} n}
    (v : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    (m : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} γ))
    : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} γ) :=
  .corec'
    (fun
      | .inl r => by
        refine comp.mk (TypeVec.splitFun ?_ ?_ <$$> comp.get r.dest)
        · exact fun i => (have := prj.get ·; prj.mk _ this)
        exact (match DTSum.equiv <| comp.get · with
          | .inl v =>
            comp.mk
              <| DTSum.cont
              <| prj.mk _
              <| .inr <| m <| ULift.down <| prj.get v
          | .inr v =>
            comp.mk <| DTSum.cont <| prj.mk _ <| .inl <| prj.get v)
      | .inr r => (TypeVec.id ::: .inr) <$$> r.dest
    )
    (Sum.inl (β := DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} γ)) v)

/- -- You can generalize it like this but i cannot be bothered -/
/- def bind {β : Type v} {γ : Type w} {α : TypeVec.{u} n} -/
/-     (v : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β)) -/
/-     (m : β → DeepThunk (uLift.{u, w} P) (α.uLift ::: ULift.{u, w} γ)) -/
/-     : DeepThunk (uLift.{u, w} P) (α.uLift ::: ULift.{u, w} γ) -/
/-     := -/
/-   .corec -/
/-     (fun -/
/-       | .inl r => sorry -/
/-       | .inr r => sorry -/
/-       ) -/
/-     (Sum.inl (β := DeepThunk (uLift.{u, w} P) (α.uLift ::: ULift.{u, w} γ)) v) -/


def flat (v : DeepThunk P (α ::: HpLuM P α)) : HpLuM P α :=
  .corec' (fun
    | .inl v => by
      refine (TypeVec.splitFun ?_ ?_)<$$> comp.get v.dest
      · exact fun i => (have := prj.get ·; this)
      exact (match DTSum.equiv <| comp.get · with
        | .inl v => .inr <| prj.get v
        | .inr v => .inl <| prj.get v)
    | .inr v => (TypeVec.id ::: .inr) <$$> v.dest)
    (Sum.inl (β := HpLuM P α) v)

def ulift_NatTrans α : uLift.{u, v} (NatTrans P) α ≃ NatTrans (uLift.{u, v} P) α :=
  comp.uLift.trans <| comp.equivTarg (fun i α => i.cases' (calc
    _ ≃ _ := comp.uLift
    _ ≃ _ := comp.equivTfn DTSum.lift
    _ ≃ _ := comp.equivTarg fun | .fz, α | .fs .fz, α => by exact prj.uLift
  ) (fun _ => by exact prj.uLift))

def ULift_down {x : Type u}
    : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift x)
    → DeepThunk P (α ::: x) :=
  HpLuM.corec fun x => by
    have := (.mp TypeVec.uLift_append1_ULift_uLift ::: id) <$$> x.dest
    have := comp.get this
    sorry
    /- transliterateMap sorry  -/

instance : MvFunctor <| DeepThunk P := HpLuM.instMvFunctor

-- Proof should be very similar to `Combinators.lean:29 / iter_eq`
theorem corec_eq {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    {v}
    : corec gen v
    = flat ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> (gen v)).ULift_down := by
  apply HpLuM.bisim (fun a b => a = b ∨ 
    ∃ im, a = corec gen im ∧ b = sorry
  )
  · right
    sorry
  · sorry

end DeepThunk

end Sme

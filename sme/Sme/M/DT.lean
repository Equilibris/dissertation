import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
import Sme.M.HpLuM
import Sme.Vec
import Sme.HEq

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

@[simp]
theorem cont_fst {α : TypeVec _} {v : α .fz} : (cont v).fst = .up .false := rfl
@[simp]
theorem recall_fst {α : TypeVec _} {v : α <| .fs .fz} : (recall v).fst = .up .true := rfl

@[simp]
theorem map_cont {α β v} (f : α ⟹ β) : f <$$> cont v = cont (f .fz v) := by
  change Sigma.mk _ _ = Sigma.mk _ _ 
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext u v
  rcases u with (_|_|_|_)
  <;> rcases v with (_|_)
  rfl

@[simp]
theorem map_recall {α β v} (f : α ⟹ β) : f <$$> recall v = recall (f (.fs .fz) v) := by
  change Sigma.mk _ _ = Sigma.mk _ _ 
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext u v
  rcases u with (_|_|_|_)
  <;> rcases v with (_|_)
  rfl

def elim {α β} (l : α .fz → β) (r : α (.fs .fz) → β) : DTSum α → β
  | ⟨.up .false, f⟩ => l <| f .fz .unit
  | ⟨.up .true, f⟩ =>  r <| f (.fs .fz) .unit

@[simp]
theorem elim_cont {α : TypeVec _} {β} (l : α .fz → β) (r : α (.fs .fz) → β) (v : α .fz)
    : elim l r (cont v) = l v := rfl
@[simp]
theorem elim_recall {α : TypeVec _} {β} (l : α .fz → β) (r : α (.fs .fz) → β) (v : α (.fs .fz))
    : elim l r (recall v) = r v := rfl

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

def lift : NatIso (uLift.{u, v} DTSum) DTSum where
  equiv := (calc
    _ ≃ _ := uEqSum.equiv
    _ ≃ _ := eqSum.equiv.symm)
  nat' x := by
    rcases x with ⟨_|_, x⟩
    <;> refine Sigma.ext (by rfl) <| heq_of_eq ?_
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> rcases h with (_|_)
    <;> rfl

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

instance {n} {P : MvPFunctor n} : MvFunctor <| DeepThunk P := HpLuM.instMvFunctor

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
    exact fun h => comp.mk <| DTSum.cont (prj.mk _ h)

theorem dest_inject {x : HpLuM P α}
    : (inject x : DeepThunk P (α ::: β)).dest
    = comp.mk (TypeVec.splitFun
        (fun (i : Fin2 n) v => (by apply prj.mk (i.add 2) v))
        (fun v => by exact comp.mk <| DTSum.cont (prj.mk _ <| inject v)
      ) <$$> x.dest) := by
  rw [inject, HpLuM.dest_corec', ←inject, comp.map_mk]
  simp only [Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
    TypeVec.append1_get_fz, MvFunctor.map_map, TypeVec.splitFun_comp']
  unfold Function.comp TypeVec.comp
  simp only
  conv =>
    lhs; arg 1; lhs; lhs; intro i x
    rw [prj.map_mk]
    change prj.mk i.fs.fs x
  congr
  funext v
  simp [comp.map_mk]

theorem inject_map_fst {γ} {v : HpLuM P α} {f : β → γ}
    : (TypeVec.id ::: f) <$$> inject v = inject v := by
  apply HpLuM.bisim
    (fun a b => ∃ v, (TypeVec.id ::: f) <$$> inject v = a ∧ inject v = b) 
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨w, rfl, rfl⟩
  use (HpLuM.dest ((TypeVec.id ::: f) <$$> inject w)).fst
  use (HpLuM.dest ((TypeVec.id ::: f) <$$> inject w)).snd
  simp only [Nat.succ_eq_add_one, HpLuM.dest_map, dest_inject, TypeVec.drop_append1_simp,
    TypeVec.last_eq, TypeVec.append1_get_fz, map_fst, comp.mk_fst, map_snd, TypeVec.comp.get,
    Function.comp_apply, heq_eq_eq, and_self, true_and]
  rw! [dest_inject]
  simp only [Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
    TypeVec.append1_get_fz, comp.mk_fst, map_fst, map_snd, TypeVec.comp.get, Function.comp_apply,
    comp.mk_snd]
  use cast (by
    simp only [Nat.succ_eq_add_one, dest_inject, TypeVec.drop_append1_simp, TypeVec.last_eq,
      TypeVec.append1_get_fz, comp.mk_fst, map_fst, map_snd, TypeVec.comp.get, Function.comp_apply,
      HpLuM.dest_map]
    congr 3
    funext i h
    rcases i with (_|_)
    · refine Sigma.ext (by rfl) <| heq_of_eq ?_
      funext i h
      rcases i with (_|_|_|_)
      <;> rcases h with (_|_)
      simp [comp.mk_fst]
      rfl
    · rfl
  ) (HpLuM.dest (inject (β := γ) w)).snd
  simp only [Nat.succ_eq_add_one, heq_cast_iff_heq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · congr
    funext i h
    rcases i with (_|_)
    · refine Sigma.ext (by rfl) <| heq_of_eq ?_
      funext i h
      rcases i with (_|_|_|_)
      <;> rcases h with (_|_)
      simp [comp.mk_fst]
      rfl
    · rfl
  · rw! [dest_inject]
    simp [comp.mk_snd]
    rfl
  rw! (castMode := .all) [HpLuM.dest_map, dest_inject]
  rintro (_|_|i) h
  · change ∃ _, _
    rcases h with ⟨(_|i), h, (_|_|_|_), (_|_), (_|_)⟩
    change P.B w.dest.fst Fin2.fz at h
    use (w.dest.snd Fin2.fz h)
    refine ⟨rfl, ?_⟩
    rw [castFn]
    case eq₂ =>
      simp only [Nat.succ_eq_add_one, dest_inject, TypeVec.drop_append1_simp, TypeVec.last_eq,
        TypeVec.append1_get_fz, comp.mk_fst, map_fst, map_snd, TypeVec.comp.get,
        Function.comp_apply]
      rintro (_|_|i)
      <;> dsimp [HpLuM.dest_map, dest_inject, comp.mk_fst, NatTrans , comp ]
      <;> congr
      <;> funext j
      <;> rcases j with (_|j)
      <;> congr
      <;> funext h
      <;> dsimp [innerMapper, comp.mk_fst, comp]
      <;> congr
      <;> funext k
      <;> rcases k with (_|_|_|_)
      <;> simp
      <;> rfl
    rw [dcastFn]
    case eq₂ =>
      simp only [Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
        TypeVec.append1_get_fz, map_fst, comp.B_eq]
      congr
      funext j
      <;> rcases j with (_|j)
      <;> rw [dest_inject]
      <;> dsimp [comp.mk_fst]
      <;> congr
      funext b
      congr
      funext j
      <;> rcases j with (_|_|_|_)
      <;> rfl
    case eq₃ =>
      intro a b _ 
      rfl
    simp only [Nat.succ_eq_add_one, TypeVec.append1_get_fz, TypeVec.drop_append1_simp,
      TypeVec.last_eq, map_fst, Nat.reduceAdd, Vec.append1.get_fz, cast_eq]
    rw [cast_sigma_snd]
    case p =>
      funext j
      simp [comp.mk_fst]
      rcases j with (_|j)
      <;> simp [innerMapper, comp.mk_fst, dest_inject]
      <;> rw [dest_inject]
      <;> simp [comp.mk_fst]
      <;> congr
      funext b
      congr
      funext j
      rcases j with (_|_|_|_)
      <;> simp
      <;> rfl

    rw! (castMode := .all) [dest_inject]
    rw [cast_sigma_congr]
    case pa => 
      rfl
    case pb =>
      simp only [comp.mk_fst, map_fst, map_snd, TypeVec.comp.get, Function.comp_apply,
        TypeVec.splitFun.get_fz, DTSum.cont_fst, comp.B_eq, Nat.succ_eq_add_one,
        TypeVec.drop_append1_simp, TypeVec.last_eq, TypeVec.append1_get_fz, heq_eq_eq]
      funext b
      congr
      funext j
      rcases j with (_|_|_|_)
      <;> rfl
    simp only [Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
      TypeVec.append1_get_fz, cast_eq]
    rw [cast_sigma_snd]
    case p =>
      funext j
      rcases j with (_|_|_|_)
      <;> simp only [comp.mk_fst, map_fst, map_snd, TypeVec.comp.get, Function.comp_apply,
        TypeVec.splitFun.get_fz, DTSum.cont_fst, Nat.reduceAdd, Vec.append1.get_fs,
        Vec.append1.get_fz, Nat.succ_eq_add_one]
      <;> rfl
    simp
    rfl
  · change _ = _
    rcases h with ⟨(_|j), h, (_|_|_|_), (_|_), (_|_)⟩
    /- rw! [dest_inject] -/
    /- simp only [TypeVec.append1_get_fs, TypeVec.append1_get_fz, Nat.succ_eq_add_one, -/
    /-   TypeVec.drop_append1_simp, TypeVec.last_eq, map_snd, TypeVec.comp.get, -/
    /-   TypeVec.appendFun.get_fs, TypeVec.appendFun.get_fz, Function.comp_apply, map_fst] -/
    /- rw [castFn] -/
    /- case eq₂ => -/
    /-   rintro (_|_|z) -/
    /-   <;> simp [comp.mk_fst] -/
    /-   <;> congr -/
    /-   <;> funext j -/
    /-   <;> rcases j with (_|j) -/
    /-   <;> congr -/
    /-   <;> funext b -/
    /-   <;> simp -/
    /-   <;> congr -/
    /-   <;> funext j -/
    /-   <;> rcases j with (_|_|_|_) -/
    /-   <;> simp [comp.mk_fst] -/
    /-   <;> rfl -/
    /- dsimp [comp.mk_fst, NatTrans, comp.B_eq] at h -/
    /- rcases h with ⟨(_|j), h, (_|_|_|_), (_|_), (_|_)⟩ -/
  · change _ = _
    rw! [dest_inject]
    simp [comp.mk_snd]
    rw [castFn]
    case eq₂ =>
      rintro (_|_|z)
      <;> simp [comp.mk_fst]
      <;> congr
      <;> funext j
      <;> rcases j with (_|j)
      <;> congr
      <;> funext b
      <;> simp
      <;> congr
      <;> funext j
      <;> rcases j with (_|_|_|_)
      <;> simp [comp.mk_fst]
      <;> rfl
    dsimp [comp.mk_fst, NatTrans, comp.B_eq] at h
    rcases h with ⟨(_|j), h, h'⟩
    · rcases h' with ⟨(_|_|_|_),(_|_), h'⟩
      simp [comp.mk_fst, comp.mk_snd, prj, TypeVec.repeat.get] at h'
      rcases h'
    · simp only [prj, Nat.succ_eq_add_one, Fin2.add, Nat.add_eq, Nat.add_zero, prj.fn, innerMapper,
        TypeVec.splitFun.get_fs, TypeVec.append1_get_fs] at h h'
      obtain rfl := prj.fn_eq h'
      rw [dcastFn]
      case eq₂ =>
        dsimp
        congr
        funext j
        rcases j with (_|j)
        <;> congr
        <;> funext b
        <;> simp
        <;> congr
        <;> funext j
        <;> rcases j with (_|_|_|_)
        <;> simp [comp.mk_fst]
        <;> rfl
      case eq₃ =>
        intro _ _ _
        rfl
      dsimp
      rw [cast_sigma_snd]
      case p =>
        funext j
        simp [comp.mk_fst]
        rcases j with (_|j)
        <;> simp [innerMapper, comp.mk_fst, dest_inject]
        <;> congr
        <;> funext b
        <;> congr
        <;> funext i
        <;> rcases i with (_|_|_|_)
        <;> rfl
      rw [cast_sigma_snd]
      case p =>
        funext j
        simp [comp.mk_fst, innerMapper]
        rfl
      simp
      rfl

#exit

theorem inject.injection : Function.Injective (inject : HpLuM P α → DeepThunk P (α ::: β)) := by
  stop
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
  .corec body ∘ gen
where
  body v := by
    -- TODO: This should just call comp.get, then transliterate
    have := comp.get v.dest
    refine ⟨
      this.fst.transliterate,
      (TypeVec.splitFun
        (fun i (h : _) => by exact ULift.transliterate <| prj.get h)
        fun h => .up ?_
      ) ⊚ this.snd ⊚ .transliterate
    ⟩
    apply DTSum.elim (fun v => prj.get v) (fun v => gen (prj.get v).down) (MvPFunctor.comp.get h)

@[simp]
theorem corec.body_fst {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β)) {w}
    : (corec.body gen w).fst = ULift.transliterate (comp.get (HpLuM.dest w)).fst :=
  rfl
@[simp]
theorem corec.body_snd {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β)) {w h}
    : (corec.body gen w).snd Fin2.fz { down := h }
    = .up (DTSum.elim
        (fun v ↦ prj.get v)
        (fun v ↦ gen (prj.get v).down)
        (comp.get ((comp.get (HpLuM.dest w)).snd Fin2.fz { down := h })))
    :=
  rfl

/- @[simp] -/
/- theorem corec.body_snd {β : Type v} -/
/-     (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β)) {w} -/
/-     : (corec.body gen w).snd =  -/
/-       (TypeVec.splitFun -/
/-         (fun i (h : _) => by exact ULift.transliterate <| prj.get h) -/
/-         fun h => .up ?_ -/
/-       ) ⊚ (comp.get v.dest).snd ⊚ TypeVec.Arrow.transliterate := by -/
/-   dsimp [corec.body] -/
/-   stop -/
/-   rfl -/

theorem inject_corec {x : HpLuM (P.uLift) α} {v : β}
    : corec (fun _ => inject x.uLift_up) v = x := by
  apply HpLuM.bisim (fun a b => ∃ v, a = corec (fun _ => inject b.uLift_up) v) ⟨_, rfl⟩
  rintro _ a ⟨w, rfl⟩
  sorry

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
  .corec' body (Sum.inl (β := HpLuM P α) v)
where
  body
    | .inl v => by
      refine (TypeVec.splitFun ?_ ?_) <$$> comp.get v.dest
      · exact fun i => (have := prj.get ·; this)
      refine (DTSum.elim
        (fun v => .inl <| prj.get v)
        (fun v => .inr <| prj.get v)
        <| comp.get ·)
    | .inr v => (TypeVec.id ::: .inr) <$$> v.dest

@[simp]
theorem flat.body_fst (v : DeepThunk P (α ::: HpLuM P α) ⊕ HpLuM P α)
    : (flat.body v).fst = v.elim (fun v => (comp.get (HpLuM.dest v)).fst) (·.dest.fst) := by
  rcases v with (v|v)
  <;> rfl

@[simp]
theorem flat.body_fst_inr (v : HpLuM P α)
    : (flat.body <| .inr v).fst = v.dest.fst := rfl
@[simp]
theorem flat.body_fst_inl (v : DeepThunk P (α ::: HpLuM P α))
    : (flat.body (.inl v)).fst = (comp.get (HpLuM.dest v)).fst := rfl

def ulift_NatTrans.args
    : (i : Fin2 n.succ)
    → NatIso (uLift.{u, v} <| innerMapper i) (innerMapper i)
  | .fz => comp.uLift.trans <| comp.niLift DTSum.lift <| fun
    | .fz => prj.uLift
    | .fs .fz => prj.uLift
  | .fs _ => prj.uLift

def ulift_NatTrans : NatIso (uLift.{u, v} (NatTrans P)) (NatTrans (uLift.{u, v} P)) :=
  comp.uLift.trans <| comp.niLift .refl ulift_NatTrans.args

@[simp]
theorem ulift_NatTrans_symm_fst_down_fst {α : TypeVec _} {w : (NatTrans (uLift.{u, v} P)) α}
    : (ulift_NatTrans.symm.equiv w).fst.down.fst = w.fst.fst.down :=
  rfl
@[simp]
theorem ulift_NatTrans_symm_fst {α : TypeVec _} {w : (NatTrans (uLift.{u, v} P)) α}
    : (ulift_NatTrans.symm.equiv w).fst 
    = (.up ⟨w.fst.fst.down, fun i h ↦
        ((ulift_NatTrans.args i).equiv.symm
              ⟨w.fst.snd i { down := h }, fun j b ↦ w.snd j ⟨i, ⟨{ down := h }, b⟩⟩⟩).fst.down⟩)
    :=
  rfl
  /- simp [ulift_NatTrans, NatIso.trans, NatIso.symm, comp.niLift, comp.equivTfn, comp.equivTarg, NatIso.refl, comp.equi, comp.uLift] -/
  /- rfl -/

@[simp]
theorem ulift_NatTrans_symm_snd {α : TypeVec _} {w : (NatTrans (uLift.{u, v} P)) α} {i v}
    : (ulift_NatTrans.symm.equiv w).snd (.fs (.fs i)) (ULift.up ⟨.fs i, v⟩)
    = w.snd i.fs.fs ⟨
        i.fs,
        ⟨{ down := v.fst }, cast (by simp [innerMapper, Fin2.add, prj]) PUnit.unit⟩
      ⟩ := by
  simp only [Nat.succ_eq_add_one, ulift_NatTrans, comp.uLift, Function.comp_apply, NatIso.refl,
    comp.niLift, comp.equivTfn, comp.equi, Equiv.trans_def, comp.equivTarg, NatIso.trans,
    NatIso.symm, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk, Equiv.symm_symm, Equiv.coe_fn_mk,
    Equiv.refl_symm, Equiv.refl_apply, comp.mk_fst, comp.get_fst, map_fst, map_snd, comp.get_snd,
    TypeVec.comp.get, comp.mk_snd]
  simp only [ulift_NatTrans.args, Nat.succ_eq_add_one, prj.uLift, prj.uLift_eq,
    Equiv.coe_fn_symm_mk, TypeVec.comp.get, TypeVec.uLift_down.get, Function.comp_apply]
  simp [prj.get, Fin2.add]

def uLift_up {x : Type u}
    (v : DeepThunk P (α ::: x))
    : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift x) :=
  .mpr TypeVec.uLift_append1_ULift_uLift <$$>
    (HpLuM.transpNatIso ulift_NatTrans <| HpLuM.uLift_up v)

def uLift_down {x : Type u}
    (v : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift x))
    : DeepThunk P (α ::: x) :=
  HpLuM.uLift_down <| HpLuM.transpNatIso ulift_NatTrans.symm <|
    .mp TypeVec.uLift_append1_ULift_uLift <$$> v

@[simp]
theorem uLift_down_up {x} (v : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift x))
    : uLift_up (uLift_down v) = v := by
  simp only [Nat.succ_eq_add_one, uLift_up, uLift_down, HpLuM.uLift_up_down]
  change _ <$$> (HpLuM.transpNatIso _ ((HpLuM.transpNatIso _).equiv.symm _)) = _
  simp [MvFunctor.map_map]

@[simp]
theorem uLift_up_down {x} (v : DeepThunk P (α ::: x))
    : uLift_down (uLift_up v) = v := by
  simp only [Nat.succ_eq_add_one, uLift_down, uLift_up, TypeVec.mpr_eq_mp, MvFunctor.map_map,
    TypeVec.mp_mp, TypeVec.mp_rfl, MvFunctor.id_map]
  change HpLuM.uLift_down ((HpLuM.transpNatIso _).equiv.symm _) = _
  simp

theorem cast_sigma_congr {α α' : Type u} {β : α → Type u} {γ : α' → Type u} (fst : α) (snd : β fst)
    (pa : α = α')
    (pb : β ≍ γ)
    : cast (by subst pa pb; rfl) (Sigma.mk fst snd)
    = Sigma.mk (cast pa fst) (cast (by subst pa pb; rfl : β fst = γ (cast pa fst)) snd) := by
  subst pa pb
  rfl
theorem cast_sigma_snd {α : Type _} {β γ : α → Type _} (fst : α) (snd : β fst)
    {p : β = γ}
    : cast (congr rfl p) (Sigma.mk fst snd) = Sigma.mk fst (cast (congr p rfl) snd) := by
  subst p
  rfl

-- Proof should be very similar to `Combinators.lean:29 / iter_eq`
/- set_option maxHeartbeats 30000 in -/
theorem corec_eq {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    {v}
    : corec gen v
    = flat ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> (gen v)).uLift_down := by
  change HpLuM.corec _ _ = _
  apply HpLuM.bisim (fun a b => a = b ∨
    ∃ im : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β),
      a = HpLuM.corec (corec.body gen) im ∧
      b = flat ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> im).uLift_down
  )
  · exact .inr ⟨_, rfl, rfl⟩
  rintro s _ (rfl|⟨w, rfl, rfl⟩)
  · use s.dest.fst, s.dest.snd
    simp only [heq_eq_eq, and_self, true_and, Nat.succ_eq_add_one, exists_eq_left']
    rintro (_|_) h
    · left; rfl
    · rfl
  simp only [Nat.succ_eq_add_one, HpLuM.dest_corec, MvQPF.comp_map, uLift_down_fst, map_fst,
    corec.body_fst, ULift.transliterate_down, exists_and_left]
  use by exact (comp.get (HpLuM.dest w)).fst.down
  simp only [Nat.succ_eq_add_one, true_and]
  rw [HpLuM.dest_corec]
  simp only [uLift_down_fst, map_fst, corec.body_fst, Nat.succ_eq_add_one, ULift.transliterate_down,
    uLift_down_snd, map_snd, heq_eq_eq, exists_eq_left']
  use cast (by simp [flat, uLift_down, HpLuM.dest_map, comp.get_fst]) ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> w).uLift_down.flat.dest.snd
  simp only [flat, Nat.succ_eq_add_one, uLift_down, HpLuM.dest_corec', map_fst, flat.body_fst,
    comp.get_fst, Sum.elim_inl, HpLuM.dest_uLift_down, HpLuM.dest_transpNatIso, MvQPF.comp_map,
    uLift_down_fst, ulift_NatTrans_symm_fst_down_fst, ULift.down_inj, heq_cast_iff_heq, heq_eq_eq,
    and_true]
  rw! [MvFunctor.map_map, HpLuM.dest_map]
  simp only [map_fst, true_and]
  rintro (_|i) h
  · change _ ∨ _
    simp only [TypeVec.Arrow.uLift_arrow, TypeVec.comp.get, TypeVec.append1_get_fz,
      TypeVec.uLift_down.get, TypeVec.mp.get, TypeVec.appendFun.get_fz, TypeVec.uLift_up.get,
      Function.comp_apply, cast_eq]
    rw! [HpLuM.dest_corec']
    simp only [map_fst, flat.body_fst_inl, Nat.succ_eq_add_one, comp.get_fst, map_snd]
    rw [castFn]
    case eq₂ =>
      rintro (_|_) <;> simp [HpLuM.dest_map, comp.get_fst]
    rw [dcastFn]
    case eq₂ =>
      simp [HpLuM.dest_map, comp.get_fst]
    case eq₃ =>
      intro a b _
      rfl
    simp only [TypeVec.append1_get_fz, map_fst, flat.body_fst_inl, Nat.succ_eq_add_one,
      comp.get_fst, TypeVec.comp.get, TypeVec.appendFun.get_fz, Function.comp_apply, cast_eq]
    dsimp [flat.body]
    rw! [corec.body_snd, HpLuM.dest_uLift_down, HpLuM.dest_transpNatIso, ]
    rw [comp.get_snd]
    dsimp
    rw [ulift_NatTrans_symm_fst]
    simp
    sorry

  · -- it works
    stop
    change _ = _
    rw! [HpLuM.dest_corec']
    simp only [TypeVec.append1_get_fs, map_fst, flat.body_fst_inl, Nat.succ_eq_add_one,
      comp.get_fst, map_snd]
    rw [castFn]
    case eq₂ =>
      rintro (_|_) <;> simp [HpLuM.dest_map]
    rw [dcastFn]
    case eq₂ =>
      simp [HpLuM.dest_map]
    case eq₃ =>
      simp
    simp only [TypeVec.append1_get_fs, flat.body, Nat.succ_eq_add_one, prj.get,
      Lean.Elab.WF.paramLet, TypeVec.last_eq, Vec.append1.get_fs, Vec.append1.get_fz,
      TypeVec.append1_get_fz, cast_eq, map_snd, comp.get_fst, comp.get_snd, map_fst,
      TypeVec.comp.get, TypeVec.appendFun.get_fs, TypeVec.id.get, TypeVec.splitFun.get_fs,
      Function.comp_apply, id_eq]
    rw! [HpLuM.dest_uLift_down, HpLuM.dest_transpNatIso, HpLuM.dest_map]
    rw! (castMode := .all) [MvFunctor.map_map]
    simp only [TypeVec.Arrow.uLift_arrow, corec.body, Nat.succ_eq_add_one, comp.get_fst, Fin2.add,
      Nat.add_eq, Nat.add_zero, prj.get, TypeVec.append1_get_fs, TypeVec.last_eq,
      Vec.append1.get_fs, Vec.append1.get_fz, TypeVec.append1_get_fz, cast_eq, comp.get_snd,
      ULift.transliterate_down, TypeVec.Arrow.transliterate, TypeVec.comp.get,
      TypeVec.uLift_down.get, TypeVec.mp.get, TypeVec.appendFun.get_fs, TypeVec.id.get,
      Function.comp_id, TypeVec.splitFun.get_fs, TypeVec.uLift_up.get, Function.comp_apply,
      uLift_down_fst, map_fst, ulift_NatTrans_symm_fst_down_fst, uLift_down_snd, map_snd,
      ULift.down_inj]
    rw! (castMode := .all) [←ulift_NatTrans.symm.nat']
    simp only [Nat.succ_eq_add_one, map_fst, map_snd, TypeVec.comp.get, TypeVec.append1_get_fs,
      TypeVec.appendFun.get_fs, TypeVec.id.get, TypeVec.mp.get, Function.comp_id, Function.id_comp,
      Function.comp_apply, cast_eq]
    simp only [eqRec_eq_cast, map_fst, cast_cast]
    rw [cast_sigma_snd]
    case p =>
      simp [eqRec_eq_cast, map_fst, cast_cast]
    rw [ulift_NatTrans_symm_snd]
    simp
    stop
    simp [ulift_NatTrans, NatIso.trans, NatIso.symm, NatIso.refl, comp.uLift, comp.niLift, comp.equivTarg, comp.equi, comp.equivTfn, ulift_NatTrans.args, HpLuM.transpNatIso, prj.uLift]
    sorry
    rw! [HpLuM.dest_corec', flat.body.eq_def]
    simp [TypeVec.Arrow.uLift_arrow]
    sorry
  stop
  rw [←NatIso.nat', HpLuM.dest_map]
  simp only [map_fst, true_and]
  dsimp [flat.body]
  rw [←TypeVec.comp_assoc, TypeVec.appendFun_comp_splitFun]
  rw [HpLuM.dest_uLift_down]
  simp only [uLift_down_fst, map_fst, TypeVec.id_comp, uLift_down_snd, map_snd]
  repeat rw [HpLuM.dest_map]
  rw [MvFunctor.map_map]
  simp only [map_fst, map_snd]
  simp [TypeVec.comp_assoc, TypeVec.appendFun_comp']
  dsimp [TypeVec.Arrow.uLift_arrow]
  stop
  rw [←ulift_NatTrans.symm.nat']
  simp
  conv =>
    rhs; intro x; lhs
    rw [HpLuM.dest_map]
    skip
  rw [HpLuM.dest_map, HpLuM.dest_uLift_down]
  sorry

end DeepThunk

end Sme

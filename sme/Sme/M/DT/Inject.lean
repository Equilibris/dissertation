import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
import Sme.M.HpLuM
import Sme.M.DT.Defs
import Sme.Vec
import Sme.HEq

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {α β : Type u} {n : Nat}

namespace DeepThunk

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
      rcases j with (_|j)
      <;> rw [dest_inject]
      <;> dsimp [comp.mk_fst]
      <;> congr
      funext b
      congr
      funext j
      rcases j with (_|_|_|_)
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

end Sme.DeepThunk

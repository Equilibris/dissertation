import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
import Sme.M.HpLuM
import Sme.M.DT.Defs
import Sme.M.DT.Inject
import Sme.Vec
import Sme.HEq

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {α β : Type u} {n : Nat}

namespace DeepThunk

variable {P : MvPFunctor n.succ} {α : TypeVec n}

def Closed (x : DeepThunk P (α ::: β)) : Prop :=
    (TypeVec.id ::: fun _ => ULift.up Bool.true) <$$> x
  = (TypeVec.id ::: fun _ => ULift.up Bool.false) <$$> x

variable (x : DeepThunk P (α ::: β))

namespace Closed

theorem inject_Closed {β} {x : HpLuM P α} : Closed (inject β x) := by
  dsimp [Closed, inject]
  apply HpLuM.bisim_map (fun a b => 
    ∃ x, a = (TypeVec.id ::: fun x ↦ { down := true }) <$$> HpLuM.corec' (inject.step β) x
    ∧ b = (TypeVec.id ::: fun x ↦ { down := false }) <$$> HpLuM.corec' (inject.step β) x
  ) ⟨_, rfl, rfl⟩
  clear *-
  rintro _ _ ⟨x, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, map_fst, HpLuM.dest_map, HpLuM.dest_corec']
  rw! [MvFunctor.map_map, MvFunctor.map_map, TypeVec.appendFun_comp', TypeVec.appendFun_comp']
  simp only [TypeVec.id_comp, TypeVec.comp_id, Function.const_comp]
  rw! [MvFunctor.map_map, MvFunctor.map_map, TypeVec.appendFun_comp', TypeVec.appendFun_comp']
  simp only [TypeVec.id_comp, TypeVec.comp_id, Function.const_comp]
  rw! [←inject]
  dsimp [inject.step]
  rw! [comp.map_mk, comp.map_mk, comp.mk_bij.injective.eq_iff]
  refine ⟨Sigma.ext rfl <| heq_of_eq ?_, ?_⟩
  · funext i h
    rcases i with (_|_)
    <;> simp [comp.map_mk, Fin2.add]
  intro v
  rw! (castMode := .all) [HpLuM.dest_map, inject, HpLuM.dest_corec']
  simp only [Nat.succ_eq_add_one, eqRec_eq_cast, map_fst, map_snd, TypeVec.comp.get,
    TypeVec.append1_get_fz, TypeVec.appendFun.get_fz, Function.comp_apply, cast_cast]
  refine ⟨_, rfl, ?_⟩
  rw! [HpLuM.dest_map, HpLuM.dest_corec']
  rfl

private theorem snd_fz_h_Closed_of_Closed.helper {y} (h : x = y) z
    : (HpLuM.dest x).snd .fz z
    = (HpLuM.dest y).snd .fz (cast (h ▸ rfl) z) := by
  subst h
  rfl

theorem snd_fz_h_Closed_of_Closed
    {x : DeepThunk P (α ::: β)} (h : x.Closed) {h'}
    : Closed ((HpLuM.dest x).snd Fin2.fz h') := by
  have := snd_fz_h_Closed_of_Closed.helper _ h (cast (by simp) h')
  simp only [Nat.succ_eq_add_one, TypeVec.append1_get_fz, comp.B_eq, cast_cast] at this
  rewrite! [HpLuM.dest_map, MvPFunctor.map_snd] at this
  simp only [map_fst, cast_eq, TypeVec.comp.get, comp.B_eq, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, Function.comp_apply] at this
  rewrite! [HpLuM.dest_map, MvPFunctor.map_snd] at this
  simp only [map_fst, cast_eq, TypeVec.comp.get, comp.B_eq, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, Function.comp_apply] at this
  exact this

private theorem getNext.helper {y} (h : x = y) z
    : (comp.get (HpLuM.dest x)).snd .fz z
    = (comp.get (HpLuM.dest y)).snd .fz (cast (h ▸ rfl) z) := by
  subst h
  rfl

-- Really strange rw! doesnt work here

def getNext (hC : Closed x) (v : P.B (comp.get (HpLuM.dest x)).fst Fin2.fz)
    : DeepThunk P (α ::: β) :=
  prj.get <| DTSum.cocont (comp.get ((comp.get (HpLuM.dest x)).snd .fz v))
    fun x h' => False.elim <| by
      have h := getNext.helper _ hC (cast (by rw [HpLuM.dest_map, comp.get_map]; rfl) v)
      simp only [Nat.succ_eq_add_one, cast_cast] at h -- Removing this line crashes my computer
      repeat rewrite! [HpLuM.dest_map, cast_eq] at h
      rewrite! (castMode := .all) [comp.get_map] at h
      simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at h
      rewrite! (castMode := .all) [comp.get_map] at h
      simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at h
      rw [
        comp.get_ext_iff,
        comp.get_map, comp.get_map,
        h',
        DTSum.map_recall, DTSum.map_recall,
        ←prj.mk_get (x := x), prj.map_mk, prj.map_mk] at h
      simp at h

theorem getNext_eq (hC : Closed x) (v : P.B (comp.get (HpLuM.dest x)).fst Fin2.fz)
    : comp.get ((comp.get (HpLuM.dest x)).snd .fz v)
    = DTSum.cont (prj.mk .fz (getNext x hC v)) :=
  DTSum.eqCases
    (comp.get ((comp.get (HpLuM.dest x)).snd Fin2.fz v))
    (fun _ h => by
      simp only [Nat.succ_eq_add_one, getNext, Vec.append1.get_fz, Vec.append1.get_fs,
        DTSum.cont.inj_iff]
      rw! [h]
      simp)
    (fun _ h => by
      rw! [getNext, h]
      generalize_proofs p
      exact (p _ rfl).elim)

theorem getNext_closed (hC : Closed x) (v : P.B (comp.get (HpLuM.dest x)).fst Fin2.fz)
    : Closed (getNext x hC v) :=
  DTSum.eqCases
    (comp.get ((comp.get (HpLuM.dest x)).snd Fin2.fz v))
    (fun i h' => by
      have h := getNext.helper _ hC (cast (by rw [HpLuM.dest_map, comp.get_map]; rfl) v)
      simp only [Nat.succ_eq_add_one, cast_cast] at h
      repeat rewrite! [HpLuM.dest_map, cast_eq] at h
      rewrite! (castMode := .all) [comp.get_map] at h
      simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at h
      rewrite! (castMode := .all) [comp.get_map] at h
      simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at h
      rw [
        comp.get_ext_iff,
        comp.get_map, comp.get_map,
        h'
        ] at h
      simp only [Nat.succ_eq_add_one, DTSum.map_cont, Vec.append1.get_fz, DTSum.cont.inj_iff] at h
      simp [getNext, Nat.succ_eq_add_one, h', DTSum.cocont_cont, Closed]
      rw [←prj.mk_get (x := i) , prj.map_mk, prj.map_mk] at h
      simpa using h)
    <| fun i h => by
      dsimp [getNext]
      generalize_proofs h'
      exact False.elim (h' _ h)

def change γ (x : DeepThunk P (α ::: β)) (h : Closed x) : DeepThunk P (α ::: γ) :=
  HpLuM.corec' step ⟨x, h⟩
where
  step (x : { x : DeepThunk P _ // Closed x}) :=
    letI := comp.get (HpLuM.dest x.1)
    comp.mk ⟨
      this.fst, fun
      | .fz => fun i => by
        exact comp.mk (DTSum.cont (prj.mk .fz ⟨getNext x.1 x.2 i, getNext_closed x.1 x.2 i⟩))
      | .fs s => fun i => prj.mk (s.add 2) <| show α s from
          prj.get (i := s.add 2) <| this.snd (.fs s) i
    ⟩

namespace change

theorem change_step_eq_map
    {x : DeepThunk P (α ::: β)} (h : Closed x)
    : (TypeVec.id ::: Subtype.val) <$$> step β ⟨x, h⟩
    = x.dest := by
  simp only [Nat.succ_eq_add_one, step]
  rw [comp.map_mk, map_mk]
  apply comp.get_ext
  rw [comp.get_mk]
  refine Sigma.ext rfl <| heq_of_eq ?_
  dsimp
  funext i h
  rcases i with (_|_)
  · simp [comp.map_mk, ←getNext_eq]
  · simp [Fin2.add]

theorem change_step_fz_h_eq
    {x : DeepThunk P (α ::: β)} (h : Closed x)
    {h'}
    : (step β ⟨x, h⟩).snd .fz h'
    = ⟨
      x.dest.snd .fz <| cast (by rw [←change_step_eq_map]; rfl) h',
      snd_fz_h_Closed_of_Closed h
    ⟩ := by
  apply Subtype.ext
  simp only [Nat.succ_eq_add_one, comp.B_eq]
  rw! [←change_step_eq_map h]
  rfl

theorem noop {x : DeepThunk P (α ::: β)} (h : Closed x) : change β x h = x := by
  apply HpLuM.bisim (fun a b => ∃ h, change β b h = a) ⟨h, rfl⟩
  clear *-
  rintro _ t ⟨h, rfl⟩
  use t.dest.fst
  dsimp only [change]
  rw! [HpLuM.dest_corec']
  simp only [Nat.succ_eq_add_one, map_fst, map_snd, heq_eq_eq, true_and, comp.B_eq, exists_and_left,
    ↓existsAndEq]
  have : t.dest.fst = (@step _ _ _ α β ⟨t, h⟩).fst := by
    rw [←change_step_eq_map h]
    simp
  use (TypeVec.id ::: HpLuM.corec' (step _)) ⊚ (step _ ⟨t, h⟩).snd ⊚ TypeVec.Arrow.mp (by rw [this])
  simp only [Nat.succ_eq_add_one, TypeVec.comp.get, comp.B_eq, TypeVec.mp.get, Function.comp_apply]
  refine ⟨⟨this.symm, ?_⟩, ?_⟩
  · rw [TypeVec.heq_of_mp_mpr rfl (by rw [this])]
    simp [TypeVec.comp_assoc]
  rintro (_|i) h
  <;> simp only [TypeVec.RelLast, TypeVec.append1_get_fs,
    TypeVec.appendFun.get_fs, TypeVec.id.get, id_eq, TypeVec.appendFun.get_fz]
  · rw! [change_step_fz_h_eq]
    simp only [Nat.succ_eq_add_one, comp.B_eq, cast_cast, cast_eq, exists_prop, and_true]
    apply snd_fz_h_Closed_of_Closed
    assumption
  · rw! (castMode := .all) [←change_step_eq_map]
    rfl

theorem map_step
    {γ β δ ε h} {f : α ⟹ β}
    {f' : _ → ε} {g : _ → δ}
    : (TypeVec.appendFun (TypeVec.appendFun f g ) f') <$$> step γ ⟨x, h⟩
    = (TypeVec.appendFun (TypeVec.appendFun f id) f') <$$> step δ ⟨x, h⟩ := by
  apply comp.get_ext
  simp only [Nat.succ_eq_add_one, step, comp.map_mk, map_mk, comp.get_mk]
  refine Sigma.ext rfl <| heq_of_eq ?_
  funext i h
  rcases i with (_|_)
  <;> dsimp at h
  <;> simp only [Fin2.add, Nat.add_eq, Nat.add_zero, TypeVec.comp.get, Function.comp_apply,
    prj.map_mk, TypeVec.appendFun.get_fs]
  simp [comp.map_mk]

theorem closed {γ} {x : DeepThunk P (α ::: β)} (h : Closed x) : (change γ x h).Closed := by
  dsimp [Closed, change]
  apply HpLuM.bisim_map (fun a b => ∃ x,
    a = (TypeVec.id ::: fun x ↦ { down := true }) <$$> HpLuM.corec' (step γ) x  ∧
    b = (TypeVec.id ::: fun x ↦ { down := false }) <$$> HpLuM.corec' (step γ) x)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨x, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, map_fst, HpLuM.dest_map]
  rw! [MvFunctor.map_map, TypeVec.appendFun_comp', MvFunctor.map_map, TypeVec.appendFun_comp']
  simp only [TypeVec.id_comp, Function.const_comp]
  rw! [HpLuM.dest_corec', HpLuM.dest_corec']
  rw! [MvFunctor.map_map, TypeVec.appendFun_comp', MvFunctor.map_map, TypeVec.appendFun_comp']
  simp only [TypeVec.comp_id, Function.const_comp]
  refine ⟨?_, ?_⟩
  · rw [map_step]
    symm
    rw [map_step]
  intro v
  rw! (castMode := .all) [HpLuM.dest_map, HpLuM.dest_corec']
  simp only [eqRec_eq_cast, map_fst, Nat.succ_eq_add_one, map_snd, TypeVec.comp.get,
    TypeVec.append1_get_fz, TypeVec.appendFun.get_fz, Function.comp_apply, cast_cast]
  refine ⟨_, rfl, ?_⟩
  rw! (castMode := .all) [HpLuM.dest_map, HpLuM.dest_corec']
  simp

theorem contract {γ δ} (x : DeepThunk P (α ::: β)) (h : Closed x) : change δ (change γ x h) (closed h) = (change δ x h) := by
  dsimp [change]
  apply HpLuM.bisim_map (fun a b => ∃ x,
    a = HpLuM.corec' (step δ) ⟨HpLuM.corec' (step γ) x, closed x.2⟩ ∧
    b = HpLuM.corec' (step δ) x)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨x, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, map_fst, Subtype.exists, HpLuM.dest_corec']
  rw! [MvFunctor.map_map, TypeVec.appendFun_comp', MvFunctor.map_map, TypeVec.appendFun_comp']
  dsimp only [TypeVec.comp_id, Function.const_comp]
  sorry

end change

end Sme.DeepThunk.Closed

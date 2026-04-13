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

theorem map {α' β'} (x : DeepThunk P (α ::: β)) {f : _ ⟹ (α' ::: β')}
    (h : x.Closed)
    : Closed (f <$$> x) := by
  dsimp [Closed, Nat.succ_eq_add_one, TypeVec.appendFun_splitFun, ]
  rw [
    ←TypeVec.split_dropFun_lastFun f, TypeVec.appendFun_splitFun,
    MvFunctor.map_map, MvFunctor.map_map,
    TypeVec.appendFun_comp', TypeVec.appendFun_comp'
    ]
  unfold Function.comp
  dsimp
  change (_ ⊚ TypeVec.id ::: id ∘ _) <$$> _ = (_ ⊚ TypeVec.id ::: id ∘ _) <$$> _
  rw [
    ←TypeVec.appendFun_comp', ←TypeVec.appendFun_comp',
    ←MvFunctor.map_map, ←MvFunctor.map_map,
    h
  ]

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

variable {x}
theorem getNext_eq (hC : Closed x) (v : P.B (comp.get (HpLuM.dest x)).fst Fin2.fz)
    : comp.get ((comp.get (HpLuM.dest x)).snd .fz v)
    = DTSum.cont (prj.mk .fz (getNext x hC v)) :=
  DTSum.eqCases
    (comp.get ((comp.get (HpLuM.dest x)).snd Fin2.fz v))
    (fun _ h => by
      simp only [Nat.succ_eq_add_one, getNext, Vec.append1.get_fz, DTSum.cont.inj_iff]
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


theorem getNext.map {β α'} {x : DeepThunk P (α ::: β)} (h : Closed x) {f : α ⟹ α'} {v}
    : getNext ((f ::: id) <$$> x) h.map v
    = (f ::: id) <$$> getNext x h (cast (by simp [comp.get_map]) v) := by
  dsimp [getNext]
  rw! (castMode := .all) [HpLuM.dest_map, comp.get_map]
  dsimp
  rw! (castMode := .all) [comp.get_map, DTSum.cocont_map, prj.get_map]
  rfl

def extract (x : DeepThunk P (α ::: β)) (h : Closed x) : HpLuM P α :=
  .corec' step ⟨x, h⟩
where
  step (x : { x : DeepThunk P _ // Closed x}) :=
    letI := comp.get (HpLuM.dest x.1)
    ⟨
      this.fst,
      fun
      | .fz => fun i => ⟨getNext x.1 x.2 i, getNext_closed x.2 i⟩
      | .fs s => (prj.get (i := s.add 2) <| this.snd (.fs s) ·)
    ⟩

namespace extract

theorem extract_inject β {x : HpLuM P α} : extract (inject β x) inject_Closed = x := by
  apply HpLuM.bisim (fun a b => a = extract (inject β b) inject_Closed) rfl
  clear *-
  rintro _ x rfl
  dsimp [extract]
  rw! (castMode := .all) [HpLuM.dest_corec']
  simp only [map_fst, map_snd, exists_and_left]
  use (step ⟨inject β x, inject_Closed⟩).fst
  use (TypeVec.id ::: HpLuM.corec' step) ⊚ (step ⟨inject β x, inject_Closed⟩).snd
  refine ⟨⟨rfl, .refl _⟩, ?_⟩
  have : x.dest.fst = (step ⟨inject β x, inject_Closed⟩).fst := by
    simp [step, inject, comp.get_map, inject.step]
  use x.dest.snd ⊚ TypeVec.Arrow.mp (by rw [this])
  refine ⟨⟨this, ?_⟩, ?_⟩
  · rw [TypeVec.heq_of_mp_mpr rfl (by rw [this]), TypeVec.comp_assoc, TypeVec.mp_mp]
    rfl
  rintro (_|_) h
  <;> change _ = _
  <;> dsimp
  · congr
    simp only [inject, Nat.succ_eq_add_one, step, getNext, Subtype.mk.injEq]
    rw! (castMode := .all) [HpLuM.dest_corec']
    dsimp [inject.step]
    rw! (castMode := .all) [comp.map_mk, comp.get_mk]
    dsimp
    rw! (castMode := .all) [comp.map_mk, comp.get_mk]
    simp
  · simp only [inject, Nat.succ_eq_add_one, step]
    rw! (castMode := .all) [HpLuM.dest_corec']
    dsimp
    simp only [inject.step, Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
      TypeVec.append1_get_fz, comp.map_mk]
    rw! (castMode := .all) [comp.get_mk, ]
    simp [Fin2.add]

end extract

theorem inject.inj β : Function.Injective (inject (P := P) (α := α) β) := by
  intro a b h
  rw [←extract.extract_inject β (x := a)]
  rw! [h]
  rw [extract.extract_inject β (x := b)]

namespace extract

theorem extract_map {β α'} (x : DeepThunk P (α ::: β)) (h : Closed x)
    {f : α ⟹ α'}
    : f <$$> extract x h = extract ((f ::: id) <$$> x) h.map := by
  apply HpLuM.bisim_map
    (∃ x, · = f <$$> HpLuM.corec' step x ∧ · = extract ((f ::: id) <$$> x.1) x.2.map)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨⟨x, h⟩, rfl, rfl⟩
  rw! (castMode := .all) [HpLuM.dest_map, MvFunctor.map_map, TypeVec.appendFun_comp']
  dsimp [extract]
  rw! (castMode := .all) [
    HpLuM.dest_corec', HpLuM.dest_corec',
    MvFunctor.map_map, TypeVec.appendFun_comp',
    MvFunctor.map_map, TypeVec.appendFun_comp',
  ]
  dsimp [step]
  rw! (castMode := .all) [HpLuM.dest_map, comp.get_map]
  refine ⟨Sigma.ext rfl <| heq_of_eq ?_, ?_⟩
  · funext i h
    rcases i with (_|_)
    · rfl
    · rfl
  intro v
  refine ⟨_, rfl, ?_⟩
  congr
  simp only [map_fst, cast_eq, Subtype.mk.injEq]
  rw [getNext.map h, eqRec_eq_cast, cast_cast]
  rfl

theorem linv_start h
    : (TypeVec.id ::: Function.const (HpLuM (NatTrans P) (α ::: β)) PUnit.unit) 
      <$$> HpLuM.dest (inject β (extract x h)) =
      (TypeVec.id ::: Function.const (HpLuM (NatTrans P) (α ::: β)) PUnit.unit) 
      <$$> x.dest := by
  change _ <$$> (HpLuM.corec' _ _).dest = _ <$$> _
  rw [HpLuM.dest_corec', MvFunctor.map_map, TypeVec.appendFun_comp']
  change  _ <$$> comp.mk _ = _
  rw [comp.get_ext_iff, comp.map_mk, comp.get_mk, MvFunctor.map_map, TypeVec.splitFun_comp']
  dsimp [extract]
  rw [HpLuM.dest_corec', MvFunctor.map_map, comp.get_map]
  dsimp [extract.step]
  refine Sigma.ext rfl <| heq_of_eq ?_
  dsimp
  funext i h'
  rcases i with (_|_)
  <;> simp only [Fin2.add, Nat.add_eq, Nat.add_zero, TypeVec.comp.get, TypeVec.append1_get_fs,
    TypeVec.splitFun.get_fs, TypeVec.appendFun.get_fs, TypeVec.id.get, Function.comp_id,
    Function.comp_apply, prj.map_mk, id_eq, TypeVec.appendFun.get_fz, TypeVec.splitFun.get_fz,
    Function.comp_apply]
  · apply comp.get_ext
    rw [comp.get_map, comp.get_map, getNext_eq h]
    simp
  · apply prj.get.bij_iff.mp
    simp

/- example -/
/-     {x : DeepThunk P (α ::: β)} h v -/
/-     : inject β (extract (x.dest.snd Fin2.fz (cast (by -/
/-       have := (Sigma.ext_iff.mp (linv_start h)).1 -/
/-       simp only [map_fst] at this -/
/-       rw [this] -/
/-       ) v)) (snd_fz_h_Closed_of_Closed h)) -/
/-     = (HpLuM.dest (inject β (extract x h))).snd Fin2.fz v := by -/
/-   sorry -/

theorem linv {x : DeepThunk P (α ::: β)} h : inject β (extract x h) = x := by
  apply HpLuM.bisim_map (fun x y => ∃ h, inject β (extract y h) = x) ⟨_, rfl⟩
  rintro _ x ⟨h, rfl⟩
  use (linv_start h)
  intro v
  use snd_fz_h_Closed_of_Closed h
  symm
  dsimp [inject]
  rw! (castMode := .all) [HpLuM.dest_corec']
  simp only [map_snd, Nat.succ_eq_add_one, TypeVec.comp.get, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, Function.comp_apply, map_fst]
  congr 1
  apply HpLuM.ext_dest
  simp only [extract, Nat.succ_eq_add_one, inject.step, TypeVec.drop_append1_simp, TypeVec.last_eq,
    TypeVec.append1_get_fz, HpLuM.dest_corec']
  rw! [HpLuM.dest_corec', MvFunctor.map_map]
  rw! [TypeVec.splitFun_eq_appendFun, TypeVec.splitFun_comp']
  unfold Function.comp
  conv =>
    lhs
    dsimp [step]
  unfold TypeVec.comp
  -- bash zone
  stop
  simp only [eqRec_eq_cast, map_fst, TypeVec.appendFun_splitFun, TypeVec.drop_append1_simp,
    TypeVec.splitFun.get_fs, TypeVec.id.get, id_eq, TypeVec.last_eq, TypeVec.append1_get_fz,
    TypeVec.splitFun.get_fz, cast_cast]
  rcases v with ⟨(_|_),v0,(_|_|_|_), v1, (_|_)⟩
  rw! [cast_sigma_snd]
  simp [comp.mk]
  stop
  apply HpLuM.bisim_map (fun a b => 
    ∃ v,
      a = inject β (extract (x.dest.snd Fin2.fz (cast (by 
        have := (Sigma.ext_iff.mp (linv_start h)).1
        simp only [map_fst] at this
        rw [this]) v)) (snd_fz_h_Closed_of_Closed h))
      ∧ b = (HpLuM.dest (inject β (extract x h))).snd Fin2.fz v
    ) ⟨_, rfl, rfl⟩
  clear *-
  rintro _ _ ⟨v, rfl, rfl⟩
  sorry

def ext
    {x y : DeepThunk P (α ::: β)} hx hy
    (h : extract x hx = extract y hy)
    : x = y := by
  -- use the fact that inject is an injection
  have := (inject.inj β).eq_iff.mpr h
  apply inject.inj β
  apply HpLuM.bisim_map (fun x y => ∃ hx hy, extract x hx = extract y hy) ⟨_, _, h⟩
  stop
  clear *-
  intro x y ⟨hx, hy, h⟩
  sorry
  stop
  apply HpLuM.bisim (fun x y => ∃ hx hy, extract x hx = extract y hy) ⟨_, _, h⟩
  clear *-
  intro x y ⟨hx, hy, h⟩
  use x.dest.fst, x.dest.snd
  use cast sorry y.dest.snd
  simp
  sorry

end extract

def change γ (x : DeepThunk P (α ::: β)) (h : Closed x) : DeepThunk P (α ::: γ) :=
  HpLuM.corec' step ⟨x, h⟩
where
  step (x : { x : DeepThunk P _ // Closed x}) :=
    letI := comp.get (HpLuM.dest x.1)
    comp.mk ⟨
      this.fst, fun
      | .fz => fun i => by
        exact comp.mk (DTSum.cont (prj.mk .fz ⟨getNext x.1 x.2 i, getNext_closed x.2 i⟩))
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

theorem step_fst_eqs
    {x : DeepThunk P (α ::: β)} (h : Closed x)
    β γ
    : (step γ ⟨x, h⟩).fst = (step β ⟨x, h⟩).fst := by
  refine Sigma.ext rfl <| heq_of_eq ?_
  funext i h
  rcases i with (_|_)
  · refine Sigma.ext rfl <| heq_of_eq ?_
    funext i h
    rcases i with (_|_|_|_)
    <;> rfl
  · rfl

theorem change_step_fz_h_eq' {γ}
    {x : DeepThunk P (α ::: β)} (h : Closed x)
    {h'}
    : (step γ ⟨x, h⟩).snd .fz h'
    = ⟨
      x.dest.snd .fz <| cast (by
        rw [←change_step_eq_map h, MvPFunctor.map_fst]
        simp only [Nat.succ_eq_add_one, comp]
        rw [step_fst_eqs]
        ) h',
      snd_fz_h_Closed_of_Closed h
      ⟩ := by
  apply Subtype.ext
  simp only [Nat.succ_eq_add_one, comp.B_eq]
  rw! [←change_step_eq_map h]
  dsimp
  rcases h' with ⟨(_|_), h, (_|_|_|_),(_|_),_,_⟩
  rw [cast_sigma_snd (p := by rw [step_fst_eqs])]
  rw [cast_sigma_congr _ _ rfl (heq_of_eq ?x)]
  case x =>
    funext b
    dsimp [step, comp.mk] at b
    rw! (castMode := .all) [step_fst_eqs _ β]
    simp [eqRec_eq_cast]
  dsimp
  rw [cast_sigma_snd (p := ?x)]
  case x =>
    funext b
    rw! (castMode := .all) [step_fst_eqs _ β]
    rw [eqRec_eq_cast]
    simp
  simp
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

/- example {x : HpLuM P α} {γ v} -/
/-   : (HpLuM.dest (inject γ x)).snd Fin2.fz v -/
/-   = inject γ (x.dest.snd .fz (cast sorry v)) -/
/-   := sorry -/

/- theorem Sme.DeepThunk.Closed.change.extract_inject.extracted_1_8 -/
/-   {β γ : Type u} (x : DeepThunk P (α ::: β)) (h : x.Closed) -/
/-   v : -/
/-   (HpLuM.dest (inject γ (extract x h))).snd Fin2.fz v = -/
/-     inject γ (extract ((HpLuM.dest x).snd Fin2.fz (cast (by -/
/-       congr 1 -/
/-       simp only [Nat.succ_eq_add_one, inject, extract, HpLuM.dest_corec', inject.step, comp.mk, -/
/-         TypeVec.drop_append1_simp, TypeVec.last_eq, TypeVec.append1_get_fz, DTSum.cont_fst, map_fst, -/
/-         map_snd, TypeVec.comp.get, Function.comp_apply]; -/
/-       rw [HpLuM.dest_corec'] -/
/-       simp [extract.step] -/
/-       sorry -/
/-       ) v)) (snd_fz_h_Closed_of_Closed h)) := by  -/
/-     sorry -/
/-  -/
/- #exit -/
theorem extract_change {β γ} (x : DeepThunk P (α ::: β)) h
    : (extract (change γ x h) (closed h)) = extract x h := by
  /- apply HpLuM.bisim_map (fun a b => ∃ x h, -/
  /-   a = inject γ (extract x h) ∧ b = change γ x h) -/
  /-   ⟨_, h, rfl, rfl⟩ -/
  sorry

#exit

theorem extract_inject {β γ} (x : DeepThunk P (α ::: β)) h
    : inject γ (extract x h) = change γ x h := by
  apply HpLuM.bisim_map (fun a b => ∃ x h,
    a = inject γ (extract x h) ∧ b = change γ x h)
    ⟨_, h, rfl, rfl⟩
  rintro _ _ ⟨x, h, rfl, rfl⟩
  change ∃ (_ : _ <$$> (HpLuM.corec' _ _).dest = _ <$$> (HpLuM.corec' _ _).dest), _
  rw! [HpLuM.dest_corec', HpLuM.dest_corec']
  rw! [MvFunctor.map_map, MvFunctor.map_map]
  rw! [TypeVec.appendFun_comp', TypeVec.appendFun_comp']
  /- dsimp [inject.step, step] -/
  change ∃ (_ : _ <$$> comp.mk _ = _ <$$> comp.mk _), _
  rw! [comp.map_mk, comp.map_mk, comp.mk_bij.injective.eq_iff]
  rw! [MvFunctor.map_map, TypeVec.splitFun_comp']
  dsimp
  dsimp [extract]
  rw! [HpLuM.dest_corec', MvFunctor.map_map, TypeVec.splitFun_comp']
  dsimp [extract.step]
  refine ⟨Sigma.ext rfl <| heq_of_eq ?_, ?_⟩
  · dsimp
    funext i h
    rcases i with (_|_) <;> simp [Fin2.add, comp.map_mk]
  intro v
  dsimp [change]
  rw! (castMode := .all) [HpLuM.dest_corec']
  dsimp
  generalize_proofs p

  use ((step γ ⟨x, h⟩).snd Fin2.fz (cast p v)).1
  use ((step γ ⟨x, h⟩).snd Fin2.fz (cast p v)).2

  refine ⟨?_, rfl⟩
  change (HpLuM.dest (inject _ (extract _ _))).snd .fz _ = _
  rw [change_step_fz_h_eq' ]
  dsimp
  rw! [←extract]
  rw [cast_cast]
  clear *-
  stop
  rw! (castMode := .all) [HpLuM.dest_corec']
  dsimp
  congr
  dsimp [inject.step]
  rw! (castMode := .all) [HpLuM.dest_corec', MvFunctor.map_map]
  rw! [TypeVec.splitFun_eq_appendFun]
  rw! (castMode := .all) [HpLuM.dest_corec', TypeVec.comp_splitFun']
  unfold Function.comp
  simp only [TypeVec.drop_append1_simp, TypeVec.splitFun.get_fs, TypeVec.id.get, TypeVec.id_eq,
    TypeVec.comp_id, TypeVec.last_eq, TypeVec.append1_get_fz, TypeVec.splitFun.get_fz,
    eqRec_eq_cast, map_fst, Nat.succ_eq_add_one, cast_cast, HpLuM.dest_corec']
  /- simp [comp.mk] -/
  stop
  ext
  rw! (castMode := .all) [HpLuM.dest_corec']
  dsimp
  simp only [eqRec_eq_cast, map_fst, Nat.succ_eq_add_one, HpLuM.dest_corec', cast_cast,
    Subtype.coe_eta]
  congr
  simp only [inject.step, Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
    TypeVec.append1_get_fz]
  stop
  ext
  rw! (castMode := .all)[HpLuM.dest_corec']
  symm
  rw! (castMode := .all)[HpLuM.dest_corec']
  simp [step, extract.step]
  simp [comp.mk, comp.get]
  symm
  simp [TypeVec.splitFun]
  /- simp -/
  stop
  simp only [Nat.succ_eq_add_one, TypeVec.append1_get_fz, extract, inject, step,
    Lean.Elab.WF.paramLet, Subtype.coe_eta]
  rw! (castMode := .all) [HpLuM.dest_corec', HpLuM.dest_corec']
  simp only [map_snd, Nat.succ_eq_add_one, TypeVec.comp.get, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, Function.comp_apply, map_fst]
  congr
  simp [inject.step]
  rw! (castMode := .all) [HpLuM.dest_corec', HpLuM.dest_corec']
  simp [extract.step]
  rfl
  sorry
  stop
  dsimp [inject, change]
  rw! (castMode := .all) [HpLuM.dest_corec']
  simp [inject.step]
  rw! (castMode := .all) [HpLuM.dest_corec']
  simp [extract.step]
  refine ⟨_, ?_, ?_, rfl⟩
  · simp
    sorry
  · sorry

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

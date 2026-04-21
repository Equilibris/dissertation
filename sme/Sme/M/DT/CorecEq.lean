import Sme.M.DT.Corec
import Sme.M.DT.Flat
import Sme.M.DT.ULift

namespace Sme.DeepThunk

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {β : Type u} {n : Nat}
  {P : MvPFunctor n.succ} {α : TypeVec n}

-- Might be easier to do a translation from corec to corec',
-- then combine this with the corec' theorem I have.

theorem corec_eq_corec' {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    {v}
    : HpLuM.uLift_down (corec' (gen ∘ ULift.down) (.up v)) = corec gen v := by
  apply HpLuM.bisim_map
      (fun a b =>
        ∃ x,
          HpLuM.uLift_down (HpLuM.corec' (corec'.body (gen ∘ ULift.down)) x) = a ∧
          HpLuM.corec (corec.body gen) x = b)
      (⟨_, rfl, rfl⟩)
  clear v
  rintro _ _ ⟨x, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, map_fst, HpLuM.dest_uLift_down, HpLuM.dest_corec',
    HpLuM.dest_corec]
  rw! [MvPFunctor.uLift_down_nat]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.Arrow.arrow_uLift_appendFun ]
  rw! [TypeVec.comp_assoc, TypeVec.comp_assoc, ←TypeVec.comp_assoc (h := TypeVec.Arrow.mpr _) ]
  simp only [TypeVec.Arrow.arrow_uLift_id, Function.const_comp, Function.comp_const,
    TypeVec.mpr_eq_mp, TypeVec.mp_mp, TypeVec.mp_rfl, TypeVec.id_comp]
  rw! [TypeVec.appendFun_comp']
  rw! [MvFunctor.map_map]
  rw! [TypeVec.comp_assoc, TypeVec.appendFun_comp']
  simp only [TypeVec.comp_id, Function.const_comp]
  dsimp [corec'.body]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.comp_assoc]
  rw! [TypeVec.appendFun_comp_splitFun]
  simp only [TypeVec.drop_append1_simp, TypeVec.id_comp, TypeVec.last_eq, TypeVec.append1_get_fz,
    Function.const_comp]
  rw! [HpLuM.dest_corec]
  rw! [MvPFunctor.uLift_down_nat]
  rw! [TypeVec.Arrow.arrow_uLift_appendFun ]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.comp_assoc, TypeVec.comp_assoc, ←TypeVec.comp_assoc (h := TypeVec.Arrow.mpr _) ]
  simp only [uLift_down_fst, map_fst, Nat.succ_eq_add_one, corec.body_fst, ULift.transliterate_down,
    uLift_down_snd, map_snd, TypeVec.Arrow.arrow_uLift_id, Function.const_comp, Function.comp_const,
    TypeVec.mpr_eq_mp, TypeVec.mp_mp, TypeVec.mp_rfl, TypeVec.id_comp]
  rw! [TypeVec.appendFun_comp']
  simp only [TypeVec.comp_id, Function.const_comp]
  dsimp [corec.body]
  refine ⟨?_, ?_⟩
  · refine Sigma.ext rfl <| heq_of_eq ?_
    ext i h
    rcases i with (_|_)
    <;> simp [TypeVec.Arrow.uLift_arrow]
  intro v
  rw! (castMode := .all) [HpLuM.dest_uLift_down]
  dsimp [MvPFunctor.uLift_down]
  /- rw! [uLift_down_bij.injective.eq_iff] -/
  rw! [HpLuM.dest_corec']
  simp only [corec'.body, Nat.succ_eq_add_one, Lean.Elab.WF.paramLet, TypeVec.last_eq,
    TypeVec.append1_get_fz, Vec.append1.get_fs, Vec.append1.get_fz, Function.comp_apply, map_fst,
    map_snd, TypeVec.comp.get, TypeVec.appendFun.get_fz, TypeVec.splitFun.get_fz, cast_eq]
  rw [eqRec_eq_cast]
  generalize_proofs _ p p1
  obtain rfl : p = p1 := rfl
  rcases DTSum.cases' (comp.get ((comp.get (HpLuM.dest x)).snd Fin2.fz { down := cast p v }))
    with (⟨x, h⟩ | ⟨x, h⟩)
  <;> rw [h]
  <;> simp only [Nat.succ_eq_add_one, DTSum.elim_recall, DTSum.elim_cont]
  case inl => use (prj.get x)
  case inr => use gen (prj.get x).down

theorem corec'_eq {β : Type u}
    (gen : β → DeepThunk P (α ::: β))
    {v}
    : corec' gen v
    = flat ((TypeVec.id ::: corec' gen) <$$> (gen v)) := by
  change HpLuM.corec' (corec'.body gen) (gen v) = _
  generalize gen v = x; clear v
  apply HpLuM.bisim_map (fun a b =>
    a = b ∨
    ∃ x, a = HpLuM.corec' (corec'.body gen) x
      ∧ b = ((TypeVec.id ::: corec' gen) <$$> x).flat)
  · exact .inr ⟨_, rfl, rfl⟩
  clear x
  rintro _ _ (rfl|⟨w, rfl, rfl⟩)
  · simp
  simp only [Nat.succ_eq_add_one, map_fst, HpLuM.dest_corec', dest_flat, TypeVec.last_eq,
    TypeVec.append1_get_fz, Vec.append1.get_fz, HpLuM.dest_map]
  rw! [MvFunctor.map_map, MvFunctor.map_map, TypeVec.appendFun_comp', TypeVec.splitFun_comp']
  simp only [TypeVec.comp_id, Function.const_comp, TypeVec.append1_get_fs,
    TypeVec.drop_append1_simp, TypeVec.appendFun.get_fs, TypeVec.id.get, TypeVec.last_eq,
    TypeVec.append1_get_fz, TypeVec.appendFun.get_fz]
  dsimp [corec'.body]
  rw! [MvFunctor.map_map, TypeVec.appendFun_comp', TypeVec.splitFun_comp']
  dsimp
  rw! [comp.get_map, MvFunctor.map_map]
  rw! [TypeVec.comp_splitFun']
  simp only [TypeVec.drop_append1_simp, TypeVec.last_eq, TypeVec.append1_get_fz,
    Function.const_comp]
  refine ⟨rfl, ?_⟩
  -- corec case
  intro v
  dsimp [flat]
  rw! (castMode := .all) [HpLuM.dest_corec']
  simp only [eqRec_eq_cast, map_fst, map_snd, TypeVec.comp.get, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, Function.comp_apply, cast_cast]
  rcases DTSum.cases' (comp.get ((comp.get w.dest).snd .fz (cast (by simp [corec'.body]) v)))
    with (⟨x, h⟩|⟨x, h⟩)
  on_goal 1 => refine .inr ⟨prj.get x, by simp [corec'.body, h], ?_⟩
  on_goal 2 =>
    refine .inl ?_
    simp only [corec'.body, Nat.succ_eq_add_one, Lean.Elab.WF.paramLet, TypeVec.last_eq,
      TypeVec.append1_get_fz, Vec.append1.get_fs, Vec.append1.get_fz, map_fst, map_snd,
      TypeVec.comp.get, TypeVec.splitFun.get_fz, Function.comp_apply, h, DTSum.elim_recall]
  all_goals
    rw! [HpLuM.dest_corec']
    simp only [flat.body, Nat.succ_eq_add_one, Lean.Elab.WF.paramLet, TypeVec.last_eq,
      TypeVec.append1_get_fz, Vec.append1.get_fz, Vec.append1.get_fs, map_fst, map_snd,
      TypeVec.comp.get, TypeVec.appendFun.get_fz, TypeVec.splitFun.get_fz, Function.comp_apply]
    rw! [HpLuM.dest_map, comp.get_map]
    simp [corec', comp.get_map, h]

theorem uLift_down_flat'
    {x : DeepThunk (uLift P) (.uLift α ::: HpLuM (uLift P) (TypeVec.uLift.{u, v} α))}
    : x.flat.uLift_down = ((TypeVec.id ::: ULift.up ∘ HpLuM.uLift_down) <$$> x).uLift_down.flat := by
  apply HpLuM.bisim_map
      (∃ x : DeepThunk _ _,
        · = x.flat.uLift_down ∧
        · = ((TypeVec.id ::: ULift.up ∘ HpLuM.uLift_down) <$$> x).uLift_down.flat)
      ⟨_, rfl, rfl⟩
  rintro _ _ ⟨_, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, map_fst, HpLuM.dest_uLift_down, dest_flat, TypeVec.last_eq,
    TypeVec.append1_get_fz, Vec.append1.get_fz]
  rw! [MvPFunctor.uLift_down_nat]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.Arrow.arrow_uLift_appendFun]
  rw! [TypeVec.comp_assoc]
  rw! [TypeVec.comp_assoc]
  rw! [←TypeVec.comp_assoc (h := TypeVec.Arrow.mpr _)]
  simp only [TypeVec.Arrow.arrow_uLift_id, Function.const_comp, Function.comp_const,
    TypeVec.mpr_eq_mp, TypeVec.mp_mp, TypeVec.mp_rfl, TypeVec.id_comp]
  rw! [TypeVec.appendFun_comp']
  rw! [MvFunctor.map_map]
  rw! [TypeVec.comp_assoc]
  rw! [TypeVec.appendFun_comp_splitFun]
  simp only [TypeVec.drop_append1_simp, TypeVec.comp_id, TypeVec.id_comp, TypeVec.last_eq,
    TypeVec.append1_get_fz, Function.const_comp]
  rw! [dest_flat]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.appendFun_comp_splitFun]
  simp only [Nat.succ_eq_add_one, Lean.Elab.WF.paramLet, TypeVec.last_eq, TypeVec.append1_get_fz,
    Vec.append1.get_fz, map_fst, map_snd, TypeVec.comp.get, TypeVec.splitFun.get_fz,
    Function.comp_apply, TypeVec.drop_append1_simp, TypeVec.id_comp, Function.const_comp]
  rw! [dest_uLift_down]
  simp only [Nat.succ_eq_add_one, HpLuM.dest_map]
  rw! [MvFunctor.map_map]
  rw! [MvFunctor.map_map]
  rw! [←ulift_NatTrans.symm.nat']
  simp
  stop
  rw! [←MvPFunctor.uLift_down_nat']
  rw! [comp.get_map]
  sorry

theorem uLift_down_flat
    {x : DeepThunk (uLift.{u, v} P) (TypeVec.uLift.{u, v} α ::: ULift.{v, u} (HpLuM P α))}
    : x.uLift_down.flat = HpLuM.uLift_down ((TypeVec.id ::: HpLuM.uLift_up ∘ ULift.down) <$$> x).flat := by
  apply HpLuM.bisim_map
      (∃ x : DeepThunk _ _,
        · = x.uLift_down.flat ∧
        · = HpLuM.uLift_down ((TypeVec.id ::: HpLuM.uLift_up ∘ ULift.down) <$$> x).flat)
      ⟨_, rfl, rfl⟩
  rintro _ _ ⟨_, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, map_fst, dest_flat, HpLuM.dest_uLift_down, TypeVec.last_eq,
    TypeVec.append1_get_fz, Vec.append1.get_fz, HpLuM.dest_map]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.appendFun_comp_splitFun]
  simp only [TypeVec.drop_append1_simp, TypeVec.id_comp, TypeVec.last_eq, TypeVec.append1_get_fz,
    Function.const_comp]
  rw! [MvFunctor.map_map]
  rw! [MvPFunctor.uLift_down_nat]
  rw! [TypeVec.Arrow.arrow_uLift_appendFun]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.comp_assoc]
  rw! [TypeVec.comp_assoc]
  rw! [←TypeVec.comp_assoc (h := TypeVec.Arrow.mpr _)]
  rw! [←TypeVec.comp_assoc (h := TypeVec.Arrow.mpr _)]
  simp only [TypeVec.Arrow.arrow_uLift_id, Function.const_comp, Function.comp_const,
    TypeVec.mpr_eq_mp, TypeVec.mp_mp, TypeVec.mp_rfl, TypeVec.id_comp]
  rw! [TypeVec.appendFun_comp_splitFun]
  rw! [TypeVec.appendFun_comp_splitFun]
  simp only [TypeVec.drop_append1_simp, TypeVec.id_comp, TypeVec.last_eq, TypeVec.append1_get_fz,
    Function.const_comp]
  rw! [comp.get_map]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.comp_assoc]
  rw! [TypeVec.comp_splitFun']
  simp only [TypeVec.drop_append1_simp, TypeVec.last_eq, TypeVec.append1_get_fz,
    Function.const_comp]
  rw! [dest_uLift_down]
  rw! [comp.uLift_pull_get]
  refine ⟨?_, ?_⟩
  · refine Sigma.ext rfl <| heq_of_eq ?_
    funext i h
    rcases i with (_|_)
    · rfl
    dsimp at h
    simp
    sorry
  sorry


theorem corec_eq2 {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    {v}
    : corec gen v
    = flat ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> (gen v)).uLift_down := by
  rw [←corec_eq_corec']
  rw [corec'_eq]
  change ((TypeVec.id ::: corec' (gen ∘ ULift.down)) <$$> gen v).flat.uLift_down = _
  #check corec_eq_corec'
  sorry

theorem corec_eq {β : Type v}
    (gen : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    {v}
    : corec gen v
    = flat ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> (gen v)).uLift_down := by
  stop
  rw [←corec_eq_corec']
  rw [corec'_eq]
  generalize ((TypeVec.id ::: corec' (gen ∘ ULift.down)) <$$> (gen ∘ ULift.down) { down := v }) = x
  generalize ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> gen v) = y
  stop
  change HpLuM.corec _ _ = _
  apply HpLuM.bisim_map (fun a b => a = b ∨
    ∃ im : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β),
      a = HpLuM.corec (corec.body gen) im ∧
      b = flat ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> im).uLift_down
  )
  · exact .inr ⟨_, rfl, rfl⟩
  rintro s _ (rfl|⟨w, rfl, rfl⟩)
  · simp
  simp only [Nat.succ_eq_add_one, map_fst, HpLuM.dest_corec, dest_flat, TypeVec.last_eq,
    TypeVec.append1_get_fz, Vec.append1.get_fz]
  rw! [MvFunctor.map_map]
  /- rw! [MvFunctor.map_map] -/
  rw! [TypeVec.appendFun_comp_splitFun]
  simp only [TypeVec.drop_append1_simp, TypeVec.id_comp, TypeVec.last_eq,
    TypeVec.append1_get_fz, Function.const_comp]
  rw! [MvPFunctor.uLift_down_nat]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.Arrow.arrow_uLift_appendFun]
  simp only [TypeVec.Arrow.arrow_uLift_id, Function.const_comp, Function.comp_const]
  rw! [TypeVec.comp_assoc, TypeVec.comp_assoc, TypeVec.comp_assoc, ]
  rw! [←TypeVec.comp_assoc (h := TypeVec.Arrow.mpr _)]
  rw! [TypeVec.mp_mpr, TypeVec.mp_rfl, TypeVec.id_comp]
  rw! [TypeVec.appendFun_comp']
  simp only [TypeVec.comp_id, Function.const_comp]
  -- change
  rw! [uLift_down_eq_iff]
  rw! [←MvPFunctor.uLift_up_nat]
  rw! [comp.uLift_push_get]
  stop
  -- rhs
  rw! [dest_uLift_down]
  rw! [HpLuM.dest_map]
  rw! [MvFunctor.map_map]
  rw! [MvFunctor.map_map]
  rw! [TypeVec.comp_assoc]
  rw! [TypeVec.appendFun_comp']
  unfold Function.comp
  /- rw! [helper] -/
  rw! [←ulift_NatTrans.symm.nat']
  stop
  rw! [←MvPFunctor.uLift_down_nat']
  rw! [comp.get_map]
  stop
  constructor
  case w =>
    sorry
  · intro v
    sorry
  stop
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
  use cast (by simp [flat, uLift_down, HpLuM.dest_map, comp.get_fst])
    ((TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down) <$$> w).uLift_down.flat.dest.snd
  simp only [flat, Nat.succ_eq_add_one, uLift_down, HpLuM.dest_corec', map_fst, flat.body_fst,
    comp.get_fst, Sum.elim_inl, HpLuM.dest_uLift_down, HpLuM.dest_transpNatIso, MvQPF.comp_map,
    uLift_down_fst, ulift_NatTrans_symm_fst_down_fst, ULift.down_inj, heq_cast_iff_heq, heq_eq_eq,
    and_true]
  rw! [MvFunctor.map_map, HpLuM.dest_map]
  simp only [map_fst, true_and]
  rintro (_|i) h
  · change _ ∨ _
    -- TODO: Do the computation here
    left
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
    stop
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
      rintro (_|_) <;> simp [HpLuM.dest_map, comp.get_fst]
    rw [dcastFn]
    case eq₂ =>
      simp [HpLuM.dest_map, comp.get_fst]
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
    rfl
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

end Sme.DeepThunk



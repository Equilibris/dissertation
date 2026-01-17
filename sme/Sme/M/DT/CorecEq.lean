import Sme.M.DT.Corec
import Sme.M.DT.Flat
import Sme.M.DT.ULift

namespace Sme.DeepThunk

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {β : Type u} {n : Nat}
  {P : MvPFunctor n.succ} {α : TypeVec n}

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



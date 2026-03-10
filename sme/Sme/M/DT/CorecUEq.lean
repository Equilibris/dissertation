import Sme.M.DT.Corec
import Sme.M.DT.Flat
import Sme.M.DT.ULift

namespace Sme.DeepThunk

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {β : Type u} {n : Nat}
  {P : MvPFunctor n.succ} {α : TypeVec n}

theorem corec_eq {β : Type u}
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
  simp only [map_snd, TypeVec.comp.get, TypeVec.append1_get_fz, TypeVec.appendFun.get_fz,
    Function.comp_apply, map_fst]
  rw [eqRec_eq_cast]
  simp only [map_fst, cast_cast]
  generalize_proofs p pf
  rw [HpLuM.dest_corec', map_fst] at p
  rcases DTSum.cases' (comp.get ((comp.get w.dest).snd .fz (cast (by simp [corec'.body]) v)))
    with (⟨x, h⟩|⟨x, h⟩)
  case inl =>
    right
    use prj.get x
    constructor
    · simp [corec'.body, h]
    · rw! [HpLuM.dest_corec']
      simp only [flat.body, Nat.succ_eq_add_one, Lean.Elab.WF.paramLet, TypeVec.last_eq,
        TypeVec.append1_get_fz, Vec.append1.get_fz, Vec.append1.get_fs, map_fst, map_snd,
        TypeVec.comp.get, TypeVec.appendFun.get_fz, TypeVec.splitFun.get_fz, Function.comp_apply]
      rw! [HpLuM.dest_map]
      rw! [comp.get_map]
      simp only [map_fst, map_snd, TypeVec.comp.get, Function.comp_apply]
      rw! [comp.get_map]
      rw [h]
      simp
      rfl
  case inr =>
    left
    simp only [corec'.body, Nat.succ_eq_add_one, Lean.Elab.WF.paramLet, TypeVec.last_eq,
      TypeVec.append1_get_fz, Vec.append1.get_fs, Vec.append1.get_fz, map_fst, map_snd,
      TypeVec.comp.get, TypeVec.splitFun.get_fz, Function.comp_apply]
    rw [h]
    simp only [Nat.succ_eq_add_one, DTSum.elim_recall]
    rw! [HpLuM.dest_corec']
    simp only [flat.body, Nat.succ_eq_add_one, Lean.Elab.WF.paramLet, TypeVec.last_eq,
      TypeVec.append1_get_fz, Vec.append1.get_fz, Vec.append1.get_fs, map_fst, map_snd,
      TypeVec.comp.get, TypeVec.appendFun.get_fz, TypeVec.splitFun.get_fz, Function.comp_apply]
    rw! [HpLuM.dest_map]
    rw! [comp.get_map]
    simp only [map_fst, map_snd, TypeVec.comp.get, Function.comp_apply]
    rw! [comp.get_map]
    rw [h]
    simp only [Nat.succ_eq_add_one, DTSum.map_recall, Vec.append1.get_fs, Vec.append1.get_fz,
      DTSum.elim_recall, flat.body_inr]
    rw [←prj.mk_get (v := x)]
    rw [prj.map_mk]
    simp
    rfl

end Sme.DeepThunk

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

set_option pp.proofs true in
theorem dest_uLift_down
    {α : TypeVec.{u} _}
    {x : Type u}
    (v : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift x))
    : (HpLuM.dest (uLift_down v)) 
    = MvPFunctor.uLift_down
      (ulift_NatTrans.symm.equiv
        (TypeVec.Arrow.mp TypeVec.uLift_append1_ULift_uLift <$$>
          (TypeVec.Arrow.mp TypeVec.uLift_append1_ULift_uLift ::: fun x_1 ↦
              {
                down :=
                  ((HpLuM.transpNatIso ulift_NatTrans.symm).equiv
                      (TypeVec.Arrow.mp TypeVec.uLift_append1_ULift_uLift <$$> x_1)).uLift_down }) <$$>
            HpLuM.dest v)) := by
  simp only [Nat.succ_eq_add_one, uLift_down, HpLuM.dest_uLift_down, HpLuM.dest_transpNatIso,
    HpLuM.dest_map, MvQPF.comp_map]
  rw [MvFunctor.map_map, MvFunctor.map_map, TypeVec.appendFun_comp']
  simp only [TypeVec.id_comp, MvQPF.comp_map]
  rw [ulift_NatTrans.symm_nat, ulift_NatTrans.symm_nat,
    MvFunctor.map_map, MvFunctor.map_map,
    TypeVec.comp_assoc, TypeVec.appendFun_comp']
  simp only [Nat.succ_eq_add_one, TypeVec.id_comp, MvQPF.comp_map]
  unfold Function.comp
  simp

end Sme.DeepThunk


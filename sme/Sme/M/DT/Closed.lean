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

def Closed (x : DeepThunk P (α ::: β)) : Prop :=
    (TypeVec.id ::: fun _ => ULift.up Bool.true) <$$> x
  = (TypeVec.id ::: fun _ => ULift.up Bool.false) <$$> x

namespace Closed

variable (x : DeepThunk P (α ::: β))

private theorem getNext.helper {y} (h : x = y) z
    : (comp.get (HpLuM.dest x)).snd .fz z
    = (comp.get (HpLuM.dest y)).snd .fz (cast (h ▸ rfl) z) := by
  subst h
  rfl

-- Really strange rw! doesnt work here

def getNext (hC : Closed x) (v : P.B (comp.get (HpLuM.dest x)).fst Fin2.fz)
    : DeepThunk P (α ::: β) :=
  DTSum.eqCases (comp.get ((comp.get (HpLuM.dest x)).snd .fz v))
    (fun x _ => prj.get x)
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
      simp [DTSum.eqCases])
    (fun _ h => by
      rw! [getNext, h]
      dsimp [DTSum.eqCases]
      generalize_proofs p
      exact p.elim)

def getNext_closed (hC : Closed x) (v : P.B (comp.get (HpLuM.dest x)).fst Fin2.fz)
    : Closed (getNext x hC v) := by
  have h := getNext.helper _ hC (cast (by rw [HpLuM.dest_map, comp.get_map]; rfl) v)
  simp only [Nat.succ_eq_add_one, cast_cast] at h
  repeat rewrite! [HpLuM.dest_map, cast_eq] at h
  rewrite! (castMode := .all) [comp.get_map] at h
  simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at h
  rewrite! (castMode := .all) [comp.get_map] at h
  simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at h
  rw [
    comp.get_ext_iff,
    comp.get_map, comp.get_map] at h
  simp at h
  dsimp [Closed]
  dsimp [Closed] at hC
  dsimp [getNext]
  sorry

def change {γ} (x : DeepThunk P (α ::: β)) (h : Closed x) : DeepThunk P (α ::: γ) :=
  HpLuM.corec' (sorry ∘ HpLuM.dest) x

end Sme.DeepThunk.Closed

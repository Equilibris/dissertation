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

def change {γ} (x : DeepThunk P (α ::: β)) (h : Closed x) : DeepThunk P (α ::: γ) :=
  HpLuM.corec' step ⟨x, h⟩
where
  step (x : { x : DeepThunk P _ // Closed x}) :=
    have ⟨x, h⟩ := x
    letI := comp.get (HpLuM.dest x)
    comp.mk ⟨
      this.fst, fun
      | .fz, i =>
        comp.mk (DTSum.cont (prj.mk .fz ⟨getNext x h i, getNext_closed x h i⟩))
      | .fs s, i =>
        prj.mk (s.add 2) <| show α s from
          prj.get (i := s.add 2) <| this.snd (.fs s) i
    ⟩

end Sme.DeepThunk.Closed

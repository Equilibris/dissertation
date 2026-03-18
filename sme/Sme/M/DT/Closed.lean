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

private theorem closed_univ.helper {y} (h : x = y) z
    : (comp.get (HpLuM.dest x)).snd .fz z
    = (comp.get (HpLuM.dest y)).snd .fz (cast (h ▸ rfl) z) := by
  subst h
  rfl

-- Really strange rw! doesnt work here
theorem closed_univ (hC : Closed x) {v}
    : ∃ k : DeepThunk _ _,
      comp.get ((comp.get (HpLuM.dest x)).snd .fz v) = DTSum.cont (prj.mk _ k) := by
  -- Rewrite assumption
  have := closed_univ.helper _ hC (cast (by
    rw [HpLuM.dest_map, comp.get_map]
    rfl) v)
  simp only [Nat.succ_eq_add_one, cast_cast] at this
  repeat rewrite! [HpLuM.dest_map, cast_eq, ] at this
  rewrite! (castMode := .all) [comp.get_map] at this
  simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at this
  rewrite! (castMode := .all) [comp.get_map] at this
  simp only [map_snd, TypeVec.comp.get, Function.comp_apply] at this
  have h := comp.get_ext_iff.mp this; clear this
  rw [comp.get_map, comp.get_map] at h
  -- Proceed by contradiction
  by_contra hGoal
  obtain ⟨w, h'⟩ : ∃ k, comp.get ((comp.get (HpLuM.dest x)).snd Fin2.fz v) = DTSum.recall k := by
    rcases DTSum.cases' (comp.get ((comp.get (HpLuM.dest x)).snd Fin2.fz v)) with (⟨w, h⟩ | h)
    · exact (hGoal ⟨prj.get w, by simp [h]⟩).elim
    · exact h
  rw [h'] at h
  simp only [Nat.succ_eq_add_one, DTSum.map_recall, Vec.append1.get_fs, Vec.append1.get_fz,
    DTSum.recall.inj_iff] at h
  rw [←prj.mk_get (x := w), prj.map_mk, prj.map_mk] at h
  simp at h

def change {γ} (x : DeepThunk P (α ::: β)) (h : Closed x) : DeepThunk P (α ::: γ) :=
  HpLuM.corec' (sorry ∘ HpLuM.dest) x

end Sme.DeepThunk.Closed

import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
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

def flat (v : DeepThunk P (α ::: M P α)) : M P α :=
  .corec' body (Sum.inl (β := M P α) v)
where
  body
    | .inl v => by
      refine (TypeVec.splitFun ?_ ?_) <$$> comp.get v.dest
      · exact fun i => (have := prj.get ·; this)
      refine (DTSum.elim
        (fun v => .inl <| prj.get v)
        (fun v => .inr <| prj.get v)
        <| comp.get ·)
    | .inr v => (TypeVec.id ::: .inr) <$$> v.dest

@[simp]
theorem flat.body_fst (v : DeepThunk P (α ::: M P α) ⊕ M P α)
    : (flat.body v).fst = v.elim (fun v => (comp.get (M.dest v)).fst) (·.dest.fst) := by
  rcases v with (v|v)
  <;> rfl

@[simp]
theorem flat.body_fst_inr (v : M P α)
    : (flat.body <| .inr v).fst = v.dest.fst := rfl
@[simp]
theorem flat.body_fst_inl (v : DeepThunk P (α ::: M P α))
    : (flat.body (.inl v)).fst = (comp.get (M.dest v)).fst := rfl

@[simp]
theorem flat.body_inr {v : M P α} : M.corec' flat.body (Sum.inr v) = v := by
  apply M.bisim_map (fun a b => a = M.corec' flat.body (Sum.inr b)) rfl
  rintro _ t rfl
  simp only [Nat.succ_eq_add_one, map_fst, M.dest_corec', body]
  rw! [MvFunctor.map_map, MvFunctor.map_map]
  simp only [TypeVec.appendFun_comp', TypeVec.comp_id, Function.const_comp, exists_true_left]
  rw! [M.dest_corec']
  simp [body]

@[simp]
theorem dest_flat (v : DeepThunk P (α ::: M P α)) : (flat v).dest
    = TypeVec.splitFun
        (fun i => by exact (have := prj.get ·; this))
        (by exact fun v => DTSum.elim (flat ∘ prj.get) prj.get (comp.get v))
      <$$> comp.get (M.dest v) := by
  simp only [flat, Nat.succ_eq_add_one, M.dest_corec']
  rw [flat.body]
  simp only [Nat.succ_eq_add_one, TypeVec.last_eq, TypeVec.append1_get_fz, Vec.append1.get_fz,
    Vec.append1.get_fs]
  rw [MvFunctor.map_map, TypeVec.appendFun_comp_splitFun]
  simp only [TypeVec.drop_append1_simp, TypeVec.id_comp, TypeVec.last_eq, TypeVec.append1_get_fz]
  congr 2
  funext v
  dsimp only [Function.comp_apply]
  rw [DTSum.elim_comp (f := M.corec' flat.body)]
  congr 1
  funext i
  dsimp
  rw [flat.body_inr]

end Sme.DeepThunk


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

/-- Between the original functor and the ⊕-composed functor there is an injection,
    it occurs by taking the right step at every point co-recursively.

    The instances of the hof will have this defined as a coercion. -/
def inject β : HpLuM P α → DeepThunk P (α ::: β) :=
  .corec' step
where
  step v :=  by
    refine comp.mk <|
      (TypeVec.splitFun
        ?_
        ?_
      ) <$$> v.dest
    · exact (fun i h => prj.mk (i.add 2) h)
    exact fun h => comp.mk <| DTSum.cont (prj.mk _ h)

theorem dest_inject {x : HpLuM P α}
    : (inject _ x : DeepThunk P (α ::: β)).dest
    = comp.mk (TypeVec.splitFun
        (fun (i : Fin2 n) v => (by apply prj.mk (i.add 2) v))
        (fun v => by exact comp.mk <| DTSum.cont (prj.mk _ <| inject _ v)
      ) <$$> x.dest) := by
  rw [inject, HpLuM.dest_corec', ←inject, inject.step, comp.map_mk]
  simp only [Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
    TypeVec.append1_get_fz, MvFunctor.map_map, TypeVec.splitFun_comp']
  unfold Function.comp TypeVec.comp
  simp only
  conv =>
    lhs; arg 1; lhs; lhs; intro i x
    rw [prj.map_mk]
    change prj.mk i.fs.fs x
  congr
  funext v
  simp [comp.map_mk]

instance : Coe (HpLuM P α) (DeepThunk P (α ::: β)) := ⟨inject β⟩

end Sme.DeepThunk

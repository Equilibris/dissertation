import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
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

def flat (v : DeepThunk P (α ::: HpLuM P α)) : HpLuM P α :=
  .corec' body (Sum.inl (β := HpLuM P α) v)
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
theorem flat.body_fst (v : DeepThunk P (α ::: HpLuM P α) ⊕ HpLuM P α)
    : (flat.body v).fst = v.elim (fun v => (comp.get (HpLuM.dest v)).fst) (·.dest.fst) := by
  rcases v with (v|v)
  <;> rfl

@[simp]
theorem flat.body_fst_inr (v : HpLuM P α)
    : (flat.body <| .inr v).fst = v.dest.fst := rfl
@[simp]
theorem flat.body_fst_inl (v : DeepThunk P (α ::: HpLuM P α))
    : (flat.body (.inl v)).fst = (comp.get (HpLuM.dest v)).fst := rfl

end Sme.DeepThunk


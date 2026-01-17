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

def bind {β γ : Type v} {α : TypeVec.{u} n}
    (v : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} β))
    (m : β → DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} γ))
    : DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} γ) :=
  .corec'
    (fun
      | .inl r => by
        refine comp.mk (TypeVec.splitFun ?_ ?_ <$$> comp.get r.dest)
        · exact fun i => (have := prj.get ·; prj.mk _ this)
        exact (match DTSum.equiv <| comp.get · with
          | .inl v =>
            comp.mk
              <| DTSum.cont
              <| prj.mk _
              <| .inr <| m <| ULift.down <| prj.get v
          | .inr v =>
            comp.mk <| DTSum.cont <| prj.mk _ <| .inl <| prj.get v)
      | .inr r => (TypeVec.id ::: .inr) <$$> r.dest
    )
    (Sum.inl (β := DeepThunk (uLift.{u, v} P) (α.uLift ::: ULift.{u, v} γ)) v)


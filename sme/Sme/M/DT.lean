import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
import Sme.M.DT.CorecEq
import Sme.M.DT.Inject
import Sme.M.DT.Bind
import Sme.Vec
import Sme.HEq
import Mathlib.Tactic.MinImports

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {α β : Type u} {n : Nat}
instance {n} {P : MvPFunctor n} : MvFunctor <| DeepThunk P := HpLuM.instMvFunctor

namespace DeepThunk

/- theorem inject_corec {x : HpLuM (P.uLift) α} {v : β} -/
/-     : corec (fun _ => inject x.uLift_up) v = x := by -/
/-   apply HpLuM.bisim (fun a b => ∃ v, a = corec (fun _ => inject b.uLift_up) v) ⟨_, rfl⟩ -/
/-   rintro _ a ⟨w, rfl⟩ -/
/-   sorry -/

end Sme.DeepThunk

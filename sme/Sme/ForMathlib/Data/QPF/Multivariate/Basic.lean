import Mathlib.Data.QPF.Multivariate.Basic
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix

universe u v x y

namespace MvQPF

variable {n : Nat} (F : TypeVec.{u} n → Type x)

#check MvQPF

/- @[pp_with_univ] -/
/- def uLift (P : MvQPF.{u} F) : MvQPF.{max u v} F where -/
/-   A := ULift P.A -/
/-   B := fun v => (P.B v.down).uLift -/

end MvQPF


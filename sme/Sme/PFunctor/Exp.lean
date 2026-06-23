import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite
import Mathlib.Order.Extension.Linear
import Sme.PFunctor.NatTrans


namespace PFunctor

open scoped MvFunctor

universe u v

variable {n : Nat}

def Exp (P Q : PFunctor.{u, u}) : PFunctor.{u, u} where
  A := (x : P.A → Q.A) × ∀ i, Q.B (x i) → PUnit ⊕ P.B i
  B x := (i : P.A) × { d : Q.B (x.1 i) // x.2 i (d) = .inl .unit }

end PFunctor

namespace MvPFunctor

open scoped MvFunctor

universe u

variable {n : Nat}

def Exp (P Q : MvPFunctor n) : MvPFunctor n where
  A := sorry
  B := sorry


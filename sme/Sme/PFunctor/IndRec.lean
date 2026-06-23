import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.PFunctor.Multivariate.W
import Mathlib.Order.Extension.Linear

namespace MvPFunctor

open scoped MvFunctor

universe u v

variable {n : Nat}

def IndRec
    (P : MvPFunctor.{u} (n + 2))
    (alg : ∀ α, P (α ::: (Sort u)) → Sort u)
    : (X : MvPFunctor.{u} n) × (∀ α, X α → Sort u) := by
  have := P.wp
  sorry



import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.ForMathlib.Data.ULift
import Mathlib.Control.Functor.Multivariate

universe u v w

namespace Sme

open MvPFunctor
open scoped MvFunctor

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

-- TODO: Try to remove one or both of these and replace them with a kind of mapping
def transliterate (x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    : MvPFunctor.uLift.{u, max v w} P
        (TypeVec.uLift.{u, max v w} α ::: ULift.{max u w, v} β) where
  fst := .transliterate x.fst
  snd := (.transliterate ::: .transliterate) ⊚ x.snd ⊚ .transliterate

def liftAppend {β} (v : P (α ::: β))
    : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α ::: ULift.{u, max u v} (ULift β)) where
  fst := .up v.fst
  snd := (.uLift_up ::: .up ∘ .up) ⊚ v.snd ⊚ .uLift_down

end Sme

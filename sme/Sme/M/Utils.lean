import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.ForMathlib.Data.ULift
import Mathlib.Control.Functor.Multivariate

universe u v w

namespace Sme

open MvPFunctor
open scoped MvFunctor

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

def transliterateMap {γ β}
    (f : β → γ)
    (x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β))
    : MvPFunctor.uLift.{u, w} P
        (TypeVec.uLift.{u, w} α ::: γ) where
  fst := .transliterate x.fst
  snd := (.transliterate ::: f) ⊚ x.snd ⊚ .transliterate

-- TODO: Try to remove one or both of these and replace them with a kind of mapping
def transliterate
    : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β) 
    → MvPFunctor.uLift.{u, max v w} P
        (TypeVec.uLift.{u, max v w} α ::: ULift.{max u w, v} β) := 
  transliterateMap ULift.transliterate

def liftAppend {β} (x : P (α ::: β))
    : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α ::: ULift.{u, max u v} (ULift β)) :=
  ((TypeVec.id ::: ULift.up) ⊚ .mpr TypeVec.uLift_append1_ULift_uLift)
    <$$> uLift_up x

end Sme

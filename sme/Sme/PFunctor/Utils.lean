import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.ForMathlib.Data.ULift
import Mathlib.Control.Functor.Multivariate

universe u v w

namespace Sme

open MvPFunctor
open scoped MvFunctor

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

@[inline]
def transliterateMap {γ β}
    (f : β → γ)
    (x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β))
    : MvPFunctor.uLift.{u, w} P
        (TypeVec.uLift.{u, w} α ::: γ) where
  fst := .transliterate x.fst
  snd := (TypeVec.appendFun .transliterate f) ⊚ x.snd ⊚ .transliterate

@[simp]
theorem transliterateMap_fst
    {β γ}
    {f : β → γ}
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β)}
    : (transliterateMap f x).fst = .transliterate x.fst := rfl

@[simp]
theorem transliterateMap_snd
    {β γ}
    {f : β → γ}
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β)}
    : (transliterateMap f x).snd = (.transliterate ::: f) ⊚ x.snd ⊚ .transliterate := rfl

-- TODO: Try to remove one or both of these and replace them with a kind of mapping
@[inline]
def transliterate
    : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β)
    → MvPFunctor.uLift.{u, max v w} P
        (TypeVec.uLift.{u, max v w} α ::: ULift.{max u w, v} β) := 
  transliterateMap ULift.transliterate

@[simp]
theorem transliterate_fst
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β)}
    : (transliterate x).fst = .transliterate x.fst := rfl

@[simp]
theorem transliterate_snd
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β)}
    : (transliterate x).snd = (.transliterate ::: .transliterate) ⊚ x.snd ⊚ .transliterate := 
  rfl

@[inline]
def liftAppend {β} (x : P (α ::: β))
    : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α ::: ULift.{u, max u v} (ULift β)) :=
  ((TypeVec.id ::: ULift.up) ⊚ .mpr TypeVec.uLift_append1_ULift_uLift)
    <$$> uLift_up x

@[simp]
theorem liftAppend_fst
    {β} {x : P (α ::: β)}
    : (liftAppend x).fst = .up x.fst := rfl

@[simp]
theorem lift_append_snd
    {β} {x : P (α ::: β)}
    : (liftAppend x).snd = ((TypeVec.id ::: .up) ⊚ .mpr TypeVec.uLift_append1_ULift_uLift) 
      ⊚ x.snd.arrow_uLift := rfl

end Sme

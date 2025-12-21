import Mathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec

universe u v

namespace MvPFunctor

open MvFunctor (LiftP LiftR)
open scoped MvFunctor

variable {n m : ℕ} {P : MvPFunctor.{u} n} {α : TypeVec n} {β : TypeVec n} {arr : α ⟹ β} {z : P α}

@[simp]
theorem map_fst : (arr <$$> z).fst = z.fst := rfl

@[simp]
theorem map_snd : (arr <$$> z).snd = arr ⊚ z.snd := rfl

@[pp_with_univ]
def uLift (P : MvPFunctor.{u} n) : MvPFunctor.{max u v} n where
  A := ULift P.A
  B := fun v => (P.B v.down).uLift

variable {P : MvPFunctor.{u} n}

def uLift_down {α : TypeVec.{u} n} (h : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α)) : P α :=
  ⟨h.fst.down, h.snd.uLift_arrow⟩

def uLift_up {α : TypeVec.{u} n} (h : P α) : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α) :=
  ⟨.up h.fst, h.snd.arrow_uLift⟩

namespace comp

variable
    {P : MvPFunctor.{u} n}
    {Q : Fin2 n → MvPFunctor.{u} m}
    {α β : TypeVec.{u} m}
    {mv : P (Q · α)}

theorem map_mk {f : α ⟹ β}
    : f <$$> comp.mk mv = comp.mk ((fun _ v => f <$$> v) <$$> mv) := by
  rfl

theorem mk_bij
    : Function.Bijective (comp.mk : (P (Q · α)) → (P.comp Q) α) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    comp.get,
    comp.get_mk,
    comp.mk_get,
  ⟩
theorem get_bij
    : Function.Bijective (comp.get : (P.comp Q) α → (P (Q · α))) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    comp.mk,
    comp.mk_get,
    comp.get_mk,
  ⟩

end comp

end MvPFunctor


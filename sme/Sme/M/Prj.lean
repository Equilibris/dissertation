import Mathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec

namespace MvPFunctor
open scoped MvFunctor

variable {n : Nat}

abbrev prj.fn
    : {n : _}
    → (i : Fin2 n)
    → TypeVec n
  | _, .fz => (TypeVec.repeat _ PEmpty) ::: PUnit
  | _, .fs i => (prj.fn i) ::: PEmpty

def prj (i : Fin2 n) : MvPFunctor n where
  A := PUnit
  B := fun | .unit => prj.fn i

namespace prj

def mk.fn : {n : Nat} → {α : TypeVec n} → {i : Fin2 n} → α i → (prj.fn i) ⟹ α
  | _ + 1, _, .fz, v =>
    TypeVec.splitFun (fun _ h => (TypeVec.repeat.get.mp h).elim) fun _ => v
  | _ + 1, _, .fs _, v => TypeVec.splitFun (mk.fn v) PEmpty.elim

def mk {n : Nat} {α : TypeVec n} (i : Fin2 n) (v : α i) : (prj i) α where
  fst := .unit
  snd := mk.fn v

theorem fn_same : {n : _} → {i : Fin2 n} → prj.fn i i = PUnit
  | _, .fz => rfl
  | _, .fs s => (fn_same : fn s s = PUnit)

def succ {n β} {i : Fin2 n} {α : TypeVec n} : prj (.fs i) (α ::: β) ≃ prj i α where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end prj

end MvPFunctor


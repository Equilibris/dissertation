import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Tactic.DepRewrite
import Sme.Vec

namespace Sme

open scoped MvFunctor

universe u v w

def CurriedTypeFun : Nat → Type (max u v + 1)
  | 0 => PUnit → Type v
  | 1 => Type u → Type v
  | n+1 => Type u → CurriedTypeFun n

namespace CurriedTypeFun

def app : {n : Nat} → CurriedTypeFun.{u, v} n → TypeVec.{u} n → Type v
  | 0, h, _ => h .unit
  | 1, h, v => h (v .fz)
  | _+2, h, v => app (h v.last) v.drop

abbrev ofTvF : {n : Nat} → (TypeVec.{u} n → Type v) → CurriedTypeFun.{u, v} n
  | 0, h => fun _ => h Fin2.elim0
  | 1, h => fun v => h (fun | .fz => v)
  | _+2, h => fun v => .ofTvF (fun z => h (.append1 z v))

@[simp]
theorem ofTvF_app : {n : Nat} → {t : _} → {x : TypeVec n → Type _} → (ofTvF x).app t = x t
  | 0, t, x => by
    apply congr (.refl x)
    exact funext Fin2.elim0
  | 1, t, x => by
    apply congr (.refl x)
    exact funext fun | .fz => rfl
  | n+2, t, x => by
    dsimp [ofTvF, app]
    rw [ofTvF_app]
    apply congr (.refl x)
    exact funext fun | .fz | .fs _ => rfl

abbrev append
    : {n : Nat} → (Type u → CurriedTypeFun n) → CurriedTypeFun.{u, v} n.succ 
  | 0, h => (h · .unit)
  | _+1, h => h

@[simp]
theorem append_app
    : {n : _}
    → {f : Type u → CurriedTypeFun n}
    → {t : _}
    → (CurriedTypeFun.append f).app t
    = (f t.last).app t.drop
  | 0, f, t => by simp [append, app, TypeVec.last]
  | n+1, f, t => by simp [append, app]

def comp
    {n m}
    (base : CurriedTypeFun.{u, v} n)
    (vec : Vec (CurriedTypeFun.{w, u} m) n)
    : CurriedTypeFun.{w, v} m :=
  .ofTvF fun v => base.app (vec · |>.app v)

@[simp]
theorem comp_app
    {n m}
    {base : CurriedTypeFun.{u, v} n}
    {vec : Vec (CurriedTypeFun.{w, u} m) n}
    {v}
    : (comp base vec).app v = (base.app (vec · |>.app v)) := by
  dsimp [comp]
  rw [ofTvF_app]

/-- Constant functor where the input object does not affect the output -/
def const : (n : ℕ) → (A : Type u) → CurriedTypeFun n
  | 0, A => fun _ => A
  | 1, A => fun _ => A
  | n+2, A => fun _ => const n.succ A

@[simp]
theorem const_app {A} : {n t : _} → (CurriedTypeFun.const n A).app t = A
  | 0, _ => rfl
  | 1, _ => rfl
  | n+2, _ => const_app (n := n+1)

end CurriedTypeFun

-- This ought to be generalized to involve ULifting,
-- this could be a step to liftable MvQPFs.
class EquivP (n : Nat)
    (F : CurriedTypeFun.{u, v} n)
    (P : outParam (MvPFunctor n))
    : Type max (u + 1) v where
  equiv : ∀ {t}, P t ≃ F.app t

variable {n} {F : CurriedTypeFun.{u, v} n} {P : MvPFunctor n} [EquivP n F P]

namespace EquivP

instance (priority := 100) mvf : MvFunctor F.app where
  map arr v := EquivP.equiv (arr <$$> EquivP.equiv.symm v)
instance (priority := 100) : LawfulMvFunctor F.app where
  id_map _ := by
    change EquivP.equiv _ = _
    simp
  comp_map {x y z} g h o := by
    change EquivP.equiv _ = _
    simp [MvPFunctor.comp_map, mvf]

instance const {A n} : EquivP n (.const n A) (.const n A) := ⟨{
  toFun a := cast CurriedTypeFun.const_app.symm a.fst
  invFun a := MvPFunctor.const.mk _ (cast CurriedTypeFun.const_app a)
  left_inv _ := by
    dsimp [MvPFunctor.const.mk]
    rw! [cast_cast, cast_eq]
    exact Sigma.ext (by rfl) <| heq_of_eq (funext fun _ => funext fun v => v.elim)
  right_inv _ := by
    dsimp [MvPFunctor.const.mk]
    rw! [cast_cast, cast_eq]
}⟩

instance comp
    {m n} {baseP} {base : CurriedTypeFun n}
    [eqB : EquivP _ base baseP]
    {QP : Fin2 n → MvPFunctor.{u} m}
    {Q : Fin2 n → CurriedTypeFun m}
    [eqQ : ∀ v, EquivP _ (Q v) (QP v)]
    : EquivP m (.comp base Q) (.comp baseP QP) := ⟨{
  toFun v := cast CurriedTypeFun.comp_app.symm
    <| eqB.equiv
    <| (fun _ => (eqQ _).equiv)
    <$$> MvPFunctor.comp.get v
  invFun v := MvPFunctor.comp.mk
    <| (fun _ => (eqQ _).equiv.symm)
    <$$> (eqB.equiv.symm
    <| cast CurriedTypeFun.comp_app v)
  left_inv _ := by
    simp only [cast_cast, cast_eq, Equiv.symm_apply_apply]
    rw [MvFunctor.map_map]
    unfold TypeVec.comp
    simp
  right_inv _ := by
    simp only [MvPFunctor.comp.get_mk]
    rw [MvFunctor.map_map]
    unfold TypeVec.comp
    simp
}⟩

end Sme.EquivP

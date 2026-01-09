import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Sme.PFunctor.EquivP
import Sme.PFunctor.NatIso

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

@[simp]
theorem fn_eq {n} : {i j : Fin2 n} → fn i j → i = j
  | .fz, .fz, _ => rfl
  | .fz, .fs _, h => by
    simp [fn] at h
    exact h.elim
  | .fs i, .fs j, h => by
    dsimp at h
    obtain rfl := fn_eq h
    rfl

def mk.fn : {n : Nat} → {α : TypeVec n} → {i : Fin2 n} → α i → (prj.fn i) ⟹ α
  | _ + 1, _, .fz, v =>
    TypeVec.splitFun (fun _ h => (TypeVec.repeat.get.mp h).elim) fun _ => v
  | _ + 1, _, .fs _, v => TypeVec.splitFun (mk.fn v) PEmpty.elim

def mk {n : Nat} {α : TypeVec n} (i : Fin2 n) (v : α i) : prj i α where
  fst := .unit
  snd := mk.fn v

@[simp]
theorem fn_same : {n : _} → {i : Fin2 n} → prj.fn i i = PUnit
  | _, .fz => rfl
  | _, .fs i => fn_same (i := i)

@[simp]
theorem fn_diff : {n : _} → {i j : Fin2 n} → (h : i ≠ j) → prj.fn i j = PEmpty
  | _, .fs _, .fz, _ => rfl
  | _, .fz, .fs _, _ => by simp
  | _, .fs i, .fs j, h =>
    fn_diff (i := i) (j := j) (h <| (Fin2.fs.injEq _ _).mpr ·)

theorem fn_eq_v {n} : {i : Fin2 n} → (v : fn i i) → v = cast fn_same.symm PUnit.unit 
  | .fz, _ => rfl
  | .fs i, v =>by
    obtain rfl := fn_eq_v (i := i) v
    rfl

@[simp]
theorem mk.fn_same
    : {n : Nat}
    → {α : TypeVec n}
    → {i : Fin2 n}
    → {v : α i}
    → mk.fn v i = fun _ => v
  | _, _, .fz => rfl
  | _, _, .fs i => mk.fn_same (i := i)

def get {n : Nat} {α : TypeVec n} {i : Fin2 n} (v : prj i α) : α i := 
  v.snd i (cast fn_same.symm .unit: fn i i)

def succ {n β} {i : Fin2 n} {α : TypeVec n} : prj (.fs i) (α ::: β) ≃ prj i α where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

theorem heq_const_of_unique {U T} [Subsingleton U] {u : U} {t : T} : u ≍ t ↔ U = T where
  mp h := type_eq_of_heq h
  mpr := fun h => Subsingleton.helim h u t

@[ext]
theorem ext
    {i : Fin2 n} {t}
    {x y : MvPFunctor.prj i t}
    (h : x.snd i (cast MvPFunctor.prj.fn_same.symm PUnit.unit)
    = y.snd i (cast MvPFunctor.prj.fn_same.symm PUnit.unit))
    : x = y := by
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  funext j v
  by_cases h : i = j
  · subst h
    (calc
      _ = x.snd _ _ := congr rfl (cast_eq_iff_heq.mpr (heq_const_of_unique.mpr fn_same.symm)).symm
      _ = y.snd i _ := h
      _ = y.snd i v := congr rfl (cast_eq_iff_heq.mpr (heq_const_of_unique.mpr fn_same.symm)))
  · exact ((fn_diff h).mp v).elim

@[simp]
theorem eta
    (i : Fin2 n) {t v}
    (x : MvPFunctor.prj i t)
    : MvPFunctor.prj.mk i (x.snd i v) = x := by
  ext
  simp only [mk, mk.fn_same]
  apply congr rfl
    <| eq_cast_iff_heq.mpr (heq_const_of_unique.mpr fn_same.symm).symm

@[simp]
theorem map_mk
    {n : Nat} {α β : TypeVec n} {i : Fin2 n} {v : α i}
    {f : α ⟹ β}
    : f <$$> mk i v = mk i (f i v) := by
  ext
  simp [mk, MvFunctor.map, prj, map, TypeVec.comp_get]

@[simp]
theorem get_mk
    {n : Nat} {α : TypeVec n} {i : Fin2 n} {v : α i}
    : prj.get (prj.mk i v) = v := by
  simp [mk, get]

@[simp]
theorem mk_get
    {n : Nat} {α : TypeVec n} {i : Fin2 n} {v : prj i α}
    : prj.mk i (prj.get v) = v := by
  ext
  simp [mk, get]

universe u v

def uLift_eq {α : TypeVec.{max u v} n} {i}
    : uLift.{u, v} (prj i) α ≃ prj i α where
  toFun v := prj.mk i
    <| v.2 i (cast
      (by simp [MvPFunctor.uLift, TypeVec.uLift, prj])
      (ULift.up.{v, u} PUnit.unit))
  invFun v :=
    ⟨.up .unit, mk.fn (prj.get v) ⊚ TypeVec.Arrow.uLift_down.{u, v}⟩
  left_inv v := by
    rcases v with ⟨(_|_), t⟩
    refine Sigma.ext (by rfl) <| heq_of_eq ?_
    funext j h
    rcases h with (⟨h⟩)
    change fn i j at h
    obtain rfl := fn_eq h
    obtain rfl := fn_eq_v h
    simp only [TypeVec.comp, get_mk, mk.fn_same]
    congr
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    apply dcongr_heq
    · exact (cast_heq _ PUnit.unit).symm
    · rintro (_|_) h _
      obtain rfl := fn_eq_v h
      simp [prj]
    · intro i h
      rw [i]

  right_inv v := by
    apply ext
    simp [mk, get, TypeVec.comp]

theorem uLift_natural
    {i : Fin2 n} {α β : TypeVec.{max u v} n}
    {f : α ⟹ β}
    {x : uLift.{u, v} (prj i) α}
    : f <$$> uLift_eq x = uLift_eq (f <$$> x) := by
  dsimp [uLift_eq]
  ext
  change prj.get _ = prj.get _
  simp [TypeVec.comp]

def uLift {i : Fin2 n} : NatIso (MvPFunctor.uLift.{u, v} (prj i)) (prj i) where
  equiv := uLift_eq
  nat' _ := uLift_natural

end MvPFunctor.prj

namespace Sme.CurriedTypeFun

def prj : {n : _} → (i : Fin2 n) → CurriedTypeFun n
  | _, .fz => .append (.const _)
  | _, .fs i => .append fun _ => prj i

@[simp]
theorem prj_app : {n : _} → {i : Fin2 n} → {t : _} → (prj i).app t = t i
  | _, .fz, t => by simp [prj, TypeVec.last]
  | _, .fs _, t => by simp only [prj, append_app, prj_app, TypeVec.drop]

instance {n i} : EquivP n (.prj i) (.prj i) := ⟨{
  toFun x := cast prj_app.symm
    <| x.snd i
    <| cast MvPFunctor.prj.fn_same.symm PUnit.unit
  invFun x := MvPFunctor.prj.mk i <| cast prj_app x
  left_inv x := by simp
  right_inv _ := by simp [MvPFunctor.prj.mk]
}⟩

end Sme.CurriedTypeFun


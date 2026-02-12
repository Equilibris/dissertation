import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Hom.Basic

import Sme.Examples.AMP.Product

import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.PFunctor.Univariate.M

universe u v w

section cat

open CategoryTheory Limits

section ex1
example : Monoid Nat where
  mul := (· * ·)
  one := 1
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  mul_assoc := Nat.mul_assoc

example : Monoid Nat where
  mul := (max · ·)
  one := 0
  mul_one := Nat.max_zero
  one_mul := Nat.zero_max
  mul_assoc := Nat.max_assoc
end ex1

section ex2
/--
info: class CommMonoid.{u} (M : Type u) : Type u
number of parameters: 1
parents:
  CommMonoid.toMonoid : Monoid M
  CommMonoid.toCommSemigroup : CommSemigroup M
fields:
  Mul.mul : M → M → M
  Semigroup.mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c)
  One.one : M
  MulOneClass.one_mul : ∀ (a : M), 1 * a = a
  MulOneClass.mul_one : ∀ (a : M), a * 1 = a
  Monoid.npow : ℕ → M → M :=
    npowRecAuto
  Monoid.npow_zero : ∀ (x : M), Monoid.npow 0 x = 1 := by
    intros; rfl
  Monoid.npow_succ : ∀ (n : ℕ) (x : M), Monoid.npow (n + 1) x = Monoid.npow n x * x := by
    intros; rfl
  CommMagma.mul_comm : ∀ (a b : M), a * b = b * a
constructor:
  CommMonoid.mk.{u} {M : Type u} [toMonoid : Monoid M] (mul_comm : ∀ (a b : M), a * b = b * a) : CommMonoid M
field notation resolution order:
  CommMonoid, Monoid, CommSemigroup, Semigroup, MulOneClass, MulOne, One, CommMagma, Mul
-/
#guard_msgs in
#print CommMonoid
end ex2

section ex34
instance {X : Sigma Monoid} : Monoid X.fst := X.snd
instance {X : Sigma CommMonoid} : CommMonoid X.fst := X.snd
instance {X : Sigma Preorder} : Preorder X.fst := X.snd

instance pre : Category (Sigma Preorder) where
  Hom a b := a.1 →o b.1
  id v := OrderHom.id
  comp f g := OrderHom.comp g f

instance mon : Category (Sigma Monoid) where
  Hom a b := a.1 →* b.1
  id v := MonoidHom.id v.1
  comp f g := MonoidHom.comp g f

instance cmon : Category (Sigma CommMonoid) where
  Hom a b := a.1 →* b.1
  id v := MonoidHom.id v.1
  comp f g := MonoidHom.comp g f

example : IsTerminal PUnit :=
  .ofUniqueHom
    (fun _ _ => .unit)
    (fun _ _ => rfl)

example : IsInitial PEmpty :=
  .ofUniqueHom
    (fun _ => PEmpty.elim)
    (fun _ _ => funext (PEmpty.elim ·))

instance : CommMonoid PUnit where
  mul _ _ := .unit
  one := .unit

  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl

  mul_comm _ _ := rfl

example : IsTerminal (C := Sigma CommMonoid) ⟨Unit, by infer_instance⟩ :=
  .ofUniqueHom
    (fun _ => {
      toFun _ := .unit
      map_one' := rfl
      map_mul' _ _ := rfl
    })
    fun _ _ => rfl

example : IsInitial (C := Sigma CommMonoid) ⟨Unit, by infer_instance⟩ :=
  .ofUniqueHom
    (fun _ => {
      toFun _ := 1
      map_one' := rfl
      map_mul' _ _ := by rw [Monoid.mul_one]
    })
    fun X x =>
      MonoidHom.ext fun
        | .unit =>
          MonoidHom.map_one x
end ex34

section e5
def Rel := Type

instance : Category Rel where
  Hom A B := A → B → Prop
  id A := Eq
  comp f g a c := ∃ b, f a b ∧ g b c

def Rel.P (a b : Rel) : Rel := a ⊕ b
def Rel.fP (a b : Rel) : P a b ⟶ a := fun x y => x = .inl y
def Rel.sP (a b : Rel) : P a b ⟶ b := fun x y => x = .inr y

def equiv {T A B} : (T ⟶ Rel.P A B) ≃ (T ⟶ A) × (T ⟶ B) where
  toFun f := ⟨fun u v => f u (.inl v), fun u v => f u (.inr v)⟩
  invFun fg a := fun | .inl v => fg.1 a v | .inr v => fg.2 a v
  right_inv := fun _ => rfl
  left_inv := fun _ => funext₂ fun | _, .inl _ | _, .inr _ => rfl

instance {a b} : IsBinaryProduct (Rel.fP a b) (Rel.sP a b) :=
  .ofUniqueHom
    (fun f g u v => match v with
      | .inl v => f u v
      | .inr v => g u v)
    (fun f g => funext₂ fun a b => by simp [Rel.fP, CategoryStruct.comp])
    (fun f g => funext₂ fun a b => by simp [Rel.sP, CategoryStruct.comp]) <| by
      rintro T f g m rfl rfl
      funext u v
      rcases v with (_|_)
      <;> simp [CategoryStruct.comp, Rel.fP, Rel.sP]
end e5

end cat

section pfun

variable {P : PFunctor}

open PFunctor

section ex6
-- I call fold rec,
-- and INDUCTIVE W
def PFunctor.W.rec {A} (alg : P.Obj A → A) (v : PFunctor.W P) : A := WType.elim A alg v
@[simp]
theorem PFunctor.W.rec_mk {A} (alg : P.Obj A → A) (v : P (PFunctor.W P))
  : W.rec alg (.mk v) = alg (W.rec alg <$> v) := rfl

def dest : W P → P (W P) := W.rec (W.mk <$> ·)

-- It makes a lot of sense to include it as implementing it using rec is very expensive,
-- this comes trom having to go through the entire structure despite only needing it at one level.q

end ex6

section ex7

-- Instead of showing the result directly,
-- I use the scottish definition of polynomial functors Σₛₕ cˢʰ,
-- which by construction is a functor,
-- therefore I instead inject the language given into the PFunctors defined here.

namespace PFunctor

def Id : PFunctor := ⟨PUnit, fun _ => PUnit⟩

namespace Id

variable {A} {v : A}

def mk : A → Id A := (⟨.unit, fun _ => ·⟩)
def dest : Id A → A := (·.2 .unit)

@[simp]
theorem map_mk {B} (f : A → B) : f <$> mk v = mk (f v) := rfl
@[simp]
theorem mk_dest : dest (mk v) = v := rfl
@[simp]
theorem dest_mk {v : Id A} : mk (dest v) = v := rfl

instance {A} : Id A ≃ A where
  toFun := dest
  invFun := mk

end Id

def Const (T : Type _) : PFunctor := ⟨T, fun _ => PEmpty⟩

namespace Const

variable {A T} {v : A}

def mk : T → Const T A := (⟨·, PEmpty.elim⟩)
def dest : Const T A → T := (·.1)

@[simp]
theorem PEmpty.elim_comp {B} (f : A → B) : f ∘ PEmpty.elim = PEmpty.elim := funext (PEmpty.elim ·)

@[simp]
theorem map_mk {B} (f : A → B) : f <$> mk v = mk v := calc
  _ = f <$> mk v := rfl
  _ = f <$> ⟨v, PEmpty.elim⟩ := rfl
  _ = ⟨v, f ∘ PEmpty.elim⟩ := rfl
  _ = ⟨v, PEmpty.elim⟩ := by rw [PEmpty.elim_comp]
  _ = mk v := rfl

@[simp]
theorem mk_dest : dest (mk (A := A) v) = v := rfl
@[simp]
theorem dest_mk {v : Const A T} : mk (dest v) = v :=
  Sigma.ext (by rfl) <| heq_of_eq <| funext (·.elim)

instance {A} : Const A T ≃ A where
  toFun := dest
  invFun := mk
  left_inv _ := by simp
  right_inv _ := rfl

end Const

def Prod (A B : PFunctor) : PFunctor := ⟨A.1 × B.1, fun ⟨u, v⟩ => A.2 u ⊕ B.2 v⟩

namespace Prod

variable {A B : PFunctor} {T T'} {f : T → T'}

def mk (u : A T) (v : B T) : Prod A B T := ⟨⟨u.1, v.1⟩, Sum.elim u.2 v.2⟩
def dest (x : Prod A B T) : A T × B T := ⟨⟨x.1.1, x.2 ∘ Sum.inl⟩, ⟨x.1.2, x.2 ∘ Sum.inr⟩⟩

@[simp]
theorem map_mk (u : A T) (v : B T) : f <$> mk u v = mk (f <$> u) (f <$> v) :=
  Sigma.ext rfl <| heq_of_eq (funext fun | .inl _ | .inr _ => rfl)

end Prod

def Coprod (A B : PFunctor) : PFunctor := ⟨A.1 ⊕ B.1, Sum.elim A.2 B.2⟩

namespace Coprod

variable {A B : PFunctor} {T T'} {f : T → T'}

def inl B (u : A T) : Coprod A B T := ⟨.inl u.1, u.2⟩
def inr A (u : B T) : Coprod A B T := ⟨.inr u.1, u.2⟩
def dest (x : Coprod A B T) : A T ⊕ B T := match x with
  | ⟨.inl a, b⟩ => .inl ⟨a, b⟩
  | ⟨.inr a, b⟩ => .inr ⟨a, b⟩

@[simp]
theorem map_inl (u : A T) : f <$> inl A u = inl A (f <$> u) := rfl
@[simp]
theorem map_inr (u : A T) : f <$> inr B u = inr B (f <$> u) := rfl

end Coprod

end PFunctor

inductive PStx where
  | id
  | prod (a b : PStx)
  | cop (a b : PStx)
  | const (T : Type u)

def PStx.denote : PStx → PFunctor
  | .id => PFunctor.Id
  | .const T => PFunctor.Const T
  | .cop a b => PFunctor.Coprod a.denote b.denote
  | .prod a b => PFunctor.Prod a.denote b.denote

end ex7

section ex8

/-

- Assume heq : (∀ i, fᵢ = h ≫ πᵢ)
  RTP: h = f*
  We begin by applying uniqueness of the limit.
  RTP: h ≫ πᵢ = f ≫ πᵢ
  We can simplify the right hand side,
  as it is a function this yields
  RTP: h ≫ πᵢ = fᵢ
  Now rewrite using `heq i`
  RTP: h ≫ πᵢ = h ≫ πᵢ
  And we are done

-/

/- #check CategoryTheory.Limits -/

end ex8

def hylo {A B}
    (coalg : A → P A) (alg : P B → B)
    [wf : WellFoundedRelation A]
    (h : ∀ x h, wf.rel ((coalg x).2 h) x)
    (v : A) : B :=
  let v := coalg v
  alg (⟨v.1, fun a => hylo coalg alg h <| v.2 a⟩)
termination_by v
decreasing_by
· apply h

theorem hylo_step {A B}
    (coalg : A → P A) (alg : P B → B)
    [wf : WellFoundedRelation A]
    (h : ∀ x h, wf.rel ((coalg x).2 h) x)
    (v : A)
    : hylo coalg alg h v = alg (hylo coalg alg h <$> coalg v) :=by
  rw [hylo]
  rfl

section qs

inductive MergeF T where
  | emp
  | one (v : Nat)
  | split (a b : T)

inductive MergeS where
  | emp
  | one (v : Nat)
  | split

def MergeP : PFunctor where
  A := MergeS
  B | .emp => Empty
    | .one _ => Empty
    | .split => Bool

namespace MergeP

variable {T}

@[match_pattern]
def emp : MergeP T := ⟨.emp, Empty.elim⟩
@[match_pattern]
def one : Nat → MergeP T := (⟨.one ·, Empty.elim⟩)
@[match_pattern]
def split : T → T → MergeP T := (⟨.split, fun | .true => · | .false => ·⟩)

def dest : MergeP T → MergeF T
  | ⟨.emp, _⟩ => .emp
  | ⟨.one n, _⟩ => .one n
  | ⟨.split, v⟩ => .split (v .true) (v .false)

def mk : MergeF T → MergeP T
  | .emp => ⟨.emp, Empty.elim⟩
  | .one v => ⟨.one v, Empty.elim⟩
  | .split t f => ⟨.split, fun | .true => t | .false => f⟩

#reduce dest <| split 0 1

end MergeP

def split {A} : List A → List A × List A
  | [] => ⟨[], []⟩
  | x :: xs =>
    have v := split xs
    ⟨v.2, x :: v.1⟩

theorem split_2 : (l : List Nat) → (sizeOf (split l).2 < sizeOf l ∨ l.length < 2)
  | [] | [_] => by simp
  | _ :: _ :: t => by
    left
    simp only [split, List.cons.sizeOf_spec, sizeOf_nat, Nat.add_lt_add_iff_left]
    obtain _|_ := split_2 t
    · omega
    match t with
    | [] | [_] => simp [split]; omega
    | _ :: _ :: _ => 
      simp at *
      omega

theorem split_1 : (l : List Nat) → (sizeOf (split l).1 < sizeOf l ∨ l = [])
  | [] => .inr rfl
  | [_] => by simp [split]; omega
  | h :: _ :: tl => .inl <| by
    simp only [split, List.cons.sizeOf_spec, sizeOf_nat]
    obtain _|rfl := split_1 tl
    · omega
    · simp [split]
      omega

def merge {A} [LT A] [DecidableLT A] : List A → List A → List A
  | xs, [] | [], xs => xs
  | x :: xs, y :: ys =>
    if x < y then
      x :: merge xs (y :: ys)
    else
      y :: merge (x :: xs) ys

def qs : List Nat → List Nat := hylo (match h : · with
   | [] => MergeP.emp
   | [o] => MergeP.one o
   | xs@(_::_::_) =>
      have s := split xs
      MergeP.split s.1 s.2)
  (fun
    | ⟨.emp, _⟩ => []
    | ⟨.one v, _⟩ => [v]
    | ⟨.split, h⟩ => merge (h .true) (h .false))
  fun x h => by
    simp_wf
    match x with
    | [] | [o] => cases h
    | h1 :: h2 :: t =>
      cases h
      <;> simp only [MergeP.split, split, List.cons.sizeOf_spec, sizeOf_nat, gt_iff_lt]
      · obtain h|h := split_2 t
        · omega
        · match t with
          | [] | [_] | [_,_] => 
            simp [split]
            omega
          | _::_::_::_ => 
            simp at h
            omega
      · obtain h|rfl := split_1 t
        · omega
        simp [split]
        omega

#eval qs [10,9,8,6,7,5,4,3,2,1]

end qs

section ex9

end ex9

end pfun


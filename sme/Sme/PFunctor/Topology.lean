import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec

namespace MvPFunctor

open scoped MvFunctor

universe u

variable {n : Nat}

def cop Dom (fam : Dom → MvPFunctor n) : MvPFunctor n where
  A := (x : Dom) × (fam x).1
  B v := (fam v.1).2 v.2

namespace cop

variable {Dom : Type _} {fam : Dom → MvPFunctor n} {α β : TypeVec n} {f : α ⟹ β}
    {x : (x : Dom) × fam x α} {a : cop Dom fam α}

def mk (v : (x : Dom) × fam x α) : cop Dom fam α where
  fst := ⟨v.1, v.2.1⟩
  snd i x := v.2.2 i x

def get (v : cop Dom fam α) : (x : Dom) × fam x α :=
  ⟨v.1.1, v.1.2, v.2⟩

@[simp]
theorem mk_get : get (mk x) = x := rfl

@[simp]
theorem get_mk : mk (get a) = a := rfl

@[simp]
theorem map_mk : f <$$> mk x = mk ⟨x.1, f <$$> x.2⟩ := rfl

@[simp]
theorem map_get : f <$$> (get a).2 = (get (f <$$> a)).2 := rfl

@[elab_as_elim]
def cases
    {motive : cop Dom fam α → Sort _}
    (mkCase : ∀ v, motive (mk v))
    (x : cop Dom fam α)
    : motive x :=
  mkCase (get x)

end cop

def prod (T : Type u) (fam : T → MvPFunctor.{u} n) : MvPFunctor.{u} n where
  A := (x : T) → (fam x).1
  B f i := (x : T) ×' (fam x).2 (f x) i

namespace prod

variable {T : Type u} {fam : T → MvPFunctor n} {α β : TypeVec n} {f : α ⟹ β}
    {x : (x : T) → fam x α} {a : prod T fam α}

def mk (v : (x : T) → fam x α) : prod T fam α where
  fst x := (v x).1
  snd i x := (v x.1).2 i x.2

def get (v : prod T fam α) (x : T) : fam x α where
  fst := v.1 x
  snd i k := v.2 i ⟨x, k⟩

@[simp]
theorem mk_get : get (mk x) = x := rfl

@[simp]
theorem get_mk : mk (get a) = a := rfl

@[simp]
theorem map_mk : f <$$> mk x = mk (f <$$> x ·) := rfl

@[simp]
theorem map_get {z} : f <$$> get a z = get (f <$$> a) z := rfl

@[elab_as_elim]
def cases
    {motive : prod T fam α → Sort _}
    (mkCase : ∀ v, motive (mk v))
    (x : prod T fam α)
    : motive x :=
  mkCase (get x)

end prod

def terminal : MvPFunctor n where
  A := PUnit
  B _ _ := PEmpty

namespace terminal

variable {α : TypeVec n}

def mk : terminal α where
  fst := .unit
  snd _ := PEmpty.elim

theorem unique {u : terminal α} : u = mk := Sigma.ext rfl
  <| heq_of_eq <| funext₂ fun _ x => x.elim

@[elab_as_elim]
def cases
    {motive : terminal α → Sort _}
    (mkCase : motive mk)
    (x : terminal α)
    : motive x :=
  unique (u := x) ▸ mkCase

end terminal

end MvPFunctor


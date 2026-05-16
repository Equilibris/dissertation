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

end cop

def prod (k : Nat) (fam : Fin k → MvPFunctor.{u} n) : MvPFunctor.{u} n where
  A := (x : Fin k) → (fam x).1
  B f i := (x : Fin k) × (fam x).2 (f x) i

namespace prod

variable {k : Nat} {fam : Fin k → MvPFunctor n} {α β : TypeVec n} {f : α ⟹ β}
    {x : (x : Fin k) → fam x α} {a : prod k fam α}

def mk (v : (x : Fin k) → fam x α) : prod k fam α where
  fst x := (v x).1
  snd i x := (v x.1).2 i x.2

def get (v : prod k fam α) (x : Fin k) : fam x α :=
  ⟨(v.1 x), fun i k => v.2 i ⟨x, k⟩ ⟩

@[simp]
theorem mk_get : get (mk x) = x := rfl

@[simp]
theorem get_mk : mk (get a) = a := rfl

@[simp]
theorem map_mk : f <$$> mk x = mk (f <$$> x ·) := rfl

@[simp]
theorem map_get {z} : f <$$> get a z = get (f <$$> a) z := rfl

end prod

end MvPFunctor


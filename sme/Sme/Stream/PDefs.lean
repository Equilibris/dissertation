import Mathlib.Data.PFunctor.Multivariate.M
import CoinductivePredicates
import Sme.ForMathlib.Data.PFunctor.Multivariate.M

universe u v

namespace PDef

-- PUnit because its exacly one constructor.
/- inductive Stream.Base' (α β : Type u) := -/
/-   | cons (hd : α) (tl : β) -/

def Stream.Base : MvPFunctor 2 := ⟨PUnit, fun _ _ => PUnit⟩

def PStream (A : Type u) := (MvPFunctor.M Stream.Base (fun _ => A))

namespace PStream

variable {A : Type u}

def hd (x : PStream A) : A :=
  x.dest.snd (.fs .fz) .unit

def tl (x : PStream A) : PStream A :=
  x.dest.snd .fz .unit

theorem dest_eq (a : PStream A) : a.dest = ⟨.unit, fun | .fz, _ => a.tl | .fs .fz, _ => a.hd⟩ := by 
  refine Sigma.ext (by rfl) <| heq_of_eq <| funext fun | .fz => ?_ | .fs .fz => ?_
  <;> funext .unit
  · change tl a = tl a
    rfl
  · change hd a = hd a
    rfl

coinductive Bisim (A : Type _) : PStream A → PStream A → Prop
  | step {a b : PStream A}
    (cont : Bisim a.tl b.tl)
    (h : a.hd = b.hd)
    : Bisim A a b

theorem bisim {a b} (h : Bisim A a b) : a = b := by
  rcases h with ⟨r, his, holds⟩
  refine MvPFunctor.M.bisim _ r ?_ a b holds
  intro a b rab
  rcases his rab with ⟨htl, hhd⟩
  rw [dest_eq, dest_eq]
  use .unit, fun | .fz, .unit => hd a
  use fun .unit => tl a, fun .unit => tl b
  refine ⟨?_, ?_, fun .unit => htl⟩
  · refine Sigma.ext (by rfl) <| heq_of_eq <| funext fun | .fz => ?_ | .fs .fz => ?_
    <;> funext .unit
    · change tl a = tl a
      rfl
    · change hd a = hd a
      rfl
  · refine Sigma.ext (by rfl) <| heq_of_eq <| funext fun | .fz => ?_ | .fs .fz => ?_
    <;> funext .unit
    · change tl b = tl b
      rfl
    · change hd b = hd a
      exact hhd.symm

def corec {A Gen : Type _} (gen : Gen → A × Gen) : Gen → PStream A :=
  .corecU _ (fun g =>
      ⟨.up .unit, fun
        | .fz,     .up .unit => .up (gen g).snd
        | .fs .fz, .up .unit => .up (gen g).fst⟩)

@[simp]
theorem corec.hd {A Gen : Type _} {gen : Gen → A × Gen} {g : Gen}
    : (corec gen g).hd = (gen g).fst := rfl

@[simp]
theorem corec.tl {A Gen : Type _} {gen : Gen → A × Gen} {g : Gen}
    : (corec gen g).tl = (corec gen (gen g).snd) := rfl

def dest (x : PStream A) : A × PStream A := ⟨x.hd, x.tl⟩

@[simp]
theorem corec.dest {A Gen : Type _} {gen : Gen → A × Gen} {g : Gen}
    : (corec gen g).dest = ((gen g).fst, corec gen (gen g).snd) := rfl

end PStream

end PDef


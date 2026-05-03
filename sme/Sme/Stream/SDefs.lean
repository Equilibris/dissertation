import CoinductivePredicates
import Mathlib.Data.Quot

namespace Sme

universe u v

structure PreStream (A : Type u) : Type (max u (v + 1)) where
  corec :: {Carr : Type v} (gen : Carr → A × Carr) (init : Carr)

namespace PreStream

def hd {A : Type u} (a : PreStream A) : A := (a.gen a.init).fst

def tl {A : Type u} (a : PreStream A) : PreStream A :=
  ⟨a.gen, (a.gen a.init).snd⟩

coinductive Bisim
    (A : Type u)
    : PreStream A
    → PreStream A
    → Prop where
  | step {a b : PreStream A}
    (cont : Bisim a.tl b.tl)
    (h : a.hd = b.hd)
    : Bisim A a b

variable {A : Type u} {a b c : PreStream.{u, v} A}

def Bisim.refl (x : PreStream A) : Bisim A x x :=
  ⟨Eq, (· ▸ .step rfl rfl), rfl⟩

def Bisim.symm (h : Bisim A a b) : Bisim A b a :=
  have ⟨r, his, rel⟩ := h
  ⟨(fun v => r v ·), (match his · with | .step ha hb => .step ha hb.symm), rel⟩

def Bisim.trans (hab : Bisim A a b) (hbc : Bisim A b c) : Bisim A a c :=
  have ⟨rab, hisab, hab⟩ := hab; have ⟨rbc, hisbc, hbc⟩ := hbc
  ⟨ (∃ b, rab · b ∧ rbc b ·),
    fun ⟨_, hax, hxb⟩ => match hisab hax, hisbc hxb with
      | .step hax e₁, .step hxb e₂ => .step ⟨_, hax, hxb⟩ (e₁.trans e₂),
    ⟨b, hab, hbc⟩ ⟩

def setoid (A : Type u) : Setoid (PreStream A) where
  r := Bisim A
  iseqv := ⟨Bisim.refl, Bisim.symm, Bisim.trans⟩

end PreStream

def SStream (A : Type u) := Quotient <| PreStream.setoid A

namespace SStream

variable {A : Type u}

def hd : SStream A → A :=
  Quotient.lift PreStream.hd
    fun _ _ ⟨_, his, rab⟩ => match his rab with | .step _ h => h

def tl : SStream A → SStream A :=
  Quotient.lift (Quotient.mk _ ∘ PreStream.tl)
    fun _ _ ⟨r, his, rab⟩ => match his rab with
      | .step h _ => Quotient.sound ⟨r, his, h⟩

def corec {A Carr : Type _}
    (gen : Carr → A × Carr)
    (init : Carr)
    : SStream A :=
  Quotient.mk _ (.corec gen init)

@[simp]
theorem corec.hd {A Carr : Type _} {gen : Carr → A × Carr} {init : Carr}
    : (corec gen init).hd = (gen init).fst := rfl

@[simp]
theorem corec.tl {A Carr : Type _} {gen : Carr → A × Carr} {init : Carr}
    : (corec gen init).tl = (corec gen (gen init).snd) := rfl

coinductive Bisim
    (A : Type _)
    : SStream A
    → SStream A
    → Prop
  | step
    {a b : SStream A}
    (cont : Bisim a.tl b.tl)
    (h : a.hd = b.hd)
    : Bisim A a b

theorem bisim {a b : SStream A} : Bisim A a b → a = b := by
  cases a, b using Quotient.ind₂; next a b =>
  rintro ⟨r, his, hhold⟩
  apply Quot.sound; change PreStream.Bisim A a b
  exact ⟨
    fun x y => r (.mk _ x) (.mk _ y),
    fun {x y} hxy => match his hxy with
      | .step htl hhd => .step htl hhd,
    hhold
  ⟩

example (x : PreStream A) : x.hd = hd (.mk (PreStream.setoid A) x) := rfl
example (x : PreStream A) : .mk _ x.tl = tl (.mk (PreStream.setoid A) x) := rfl

def dest (x : SStream A) : A × SStream A := ⟨x.hd, x.tl⟩

@[simp]
theorem corec.dest {A Carr : Type _} {gen : Carr → A × Carr} {init : Carr}
    : (corec gen init).dest = ((gen init).fst, corec gen (gen init).snd) := rfl

end SStream

end Sme


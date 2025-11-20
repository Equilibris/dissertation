import CoinductivePredicates
import Mathlib.Data.Quot

namespace Sme

universe u v

structure PreStream (A : Type u) where
  corec ::
  {Gen : Type v}
  gen : Gen → A × Gen
  g : Gen

namespace PreStream

def hd {A : Type u} (a : PreStream A) : A := (a.gen a.g).fst

def tl {A : Type u} (a : PreStream A) : PreStream A :=
  ⟨a.gen, (a.gen a.g).snd⟩

coinductive Bisim (A : Type u) : PreStream A → PreStream A → Prop where
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
  have ⟨rab, hisab, hab⟩ := hab
  have ⟨rbc, hisbc, hbc⟩ := hbc
  ⟨
    (∃ b, rab · b ∧ rbc b ·),
    fun ⟨_, hax, hxb⟩ =>
      match hisab hax, hisbc hxb with
      | .step hax e₁, .step hxb e₂ =>
        .step ⟨_, hax, hxb⟩ (e₁.trans e₂) ,
    ⟨b, hab, hbc⟩
  ⟩

def setoid (A : Type u) : Setoid (PreStream A) where
  r := Bisim A
  iseqv := ⟨Bisim.refl, Bisim.symm, Bisim.trans⟩

end PreStream

def SStream (A : Type u) := Quotient (PreStream.setoid A)

namespace SStream

variable {A : Type u} {a b c : SStream.{u, v} A}

def hd : SStream A → A :=
  Quotient.lift
    PreStream.hd
    fun _ _ ⟨_, his, rab⟩ =>
      match his rab with | .step _ h => h

def tl : SStream A → SStream A :=
  Quotient.lift (Quotient.mk _ ∘ PreStream.tl)
    fun _ _ ⟨r, his, rab⟩ =>
      match his rab with
      | .step h _ => Quotient.sound ⟨r, his, h⟩

example (x : PreStream A) : x.hd = hd (.mk (PreStream.setoid A) x) := rfl
example (x : PreStream A) : .mk _ x.tl = tl (.mk (PreStream.setoid A) x) := rfl

coinductive Bisim (A : Type _) : SStream A → SStream A → Prop
  | step {a b : SStream A}
    (cont : Bisim a.tl b.tl)
    (h : a.hd = b.hd)
    : Bisim A a b

theorem bisim {a b : SStream A} (h : Bisim A a b) : a = b := by
  induction a using Quotient.ind
  induction b using Quotient.ind

  apply Quot.sound

  change PreStream.Bisim _ _ _

  rcases h with ⟨r, his, hhold⟩
  exact ⟨
    fun x y => r (.mk _ x) (.mk _ y),
    fun {x y} hxy =>
      match his hxy with
      | .step htl hhd => .step htl hhd,
    hhold
  ⟩

def corec {A Gen : Type _} (gen : Gen → A × Gen) (g : Gen) : SStream A :=
  Quotient.mk _ (.corec gen g)

@[simp]
theorem corec.hd {A Gen : Type _} {gen : Gen → A × Gen} {g : Gen}
    : (corec gen g).hd = (gen g).fst := rfl

@[simp]
theorem corec.tl {A Gen : Type _} {gen : Gen → A × Gen} {g : Gen}
    : (corec gen g).tl = (corec gen (gen g).snd) := rfl

def dest (x : SStream A) : A × SStream A := ⟨x.hd, x.tl⟩

@[simp]
theorem corec.dest {A Gen : Type _} {gen : Gen → A × Gen} {g : Gen} : (corec gen g).dest = ((gen g).fst, corec gen (gen g).snd) := rfl

end SStream

end Sme


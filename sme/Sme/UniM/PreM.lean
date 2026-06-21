import Mathlib.Data.PFunctor.Multivariate.M
import Mathlib.Data.PFunctor.Univariate.M

section

namespace Sme

universe u v w x y z

open PFunctor

@[pp_with_univ]
structure PreM (P : PFunctor.{u, v}) : Type max u v (w + 1) where
  corec ::
  {β : Type w}
  (gen : β → P β)
  (seed : β)

namespace PreM

variable {P : PFunctor.{u, v}}

def dest (x : PreM P)
    : P (PreM P) :=
  map P (corec x.gen) (x.gen x.seed)

@[simp]
theorem dest_corec
      {β : Type w}
      (gen : β → P β)
      (seed : β)
    : (corec gen seed).dest
    = map P (corec gen) (gen seed) := rfl

/-- Bisimulation for PreM types,
    defined using the new bisim definition. -/
def IsBisim (R : PreM.{u, v, w} P → PreM.{u, v, w} P → Prop) :=
    ∀ s t, R s t →
      ∃ h : (Function.const _ PUnit.unit) <$> s.dest
          = (Function.const _ PUnit.unit) <$> t.dest,
      ∀ v, R (s.dest.snd v) (t.dest.snd (cast (by
        rw [show s.dest.fst = t.dest.fst from (Sigma.ext_iff.mp h).1]
      ) v))


/-- Bisimilarity of PreM -/
def Bisim : PreM.{u, v, w} P → PreM.{u, v, w} P → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

namespace Bisim

variable {a b c : PreM.{u, v, w} P}

theorem refl (x : PreM.{u, v, w} P) : Bisim x x :=
  ⟨Eq, fun | _, _, .refl _ => ⟨rfl, fun _ => rfl⟩, rfl⟩

theorem symm (h : Bisim a b) : Bisim b a :=
  have ⟨r, his, rab⟩ := h
  ⟨(fun a b => r b a), fun a b h =>
    have ⟨h, hrel⟩ := his _ _ h
    ⟨h.symm, fun v => by
      have := hrel <| cast (by
        rw [show b.dest.fst = a.dest.fst
          from (Sigma.ext_iff.mp h).1]) v
      rw [cast_cast, cast_eq] at this
      exact this
    ⟩ , rab⟩

theorem trans (hab : Bisim a b) (hbc : Bisim b c) : Bisim a c :=
  have ⟨r₁, hisAb, rab⟩ := hab
  have ⟨r₂, hisBc, rbc⟩ := hbc
  ⟨(fun a c => ∃ b, r₁ a b ∧ r₂ b c),
    fun | x, z, ⟨y, rxy, ryz⟩ => (by
      have ⟨hxy, hxyrel⟩ := hisAb _ _ rxy
      have ⟨hyz, hyzrel⟩ := hisBc _ _ ryz
      refine ⟨hxy.trans hyz, fun v => ⟨_, (hxyrel v), ?_⟩⟩
      have := (hyzrel <| cast (by
        rw [show x.dest.fst = y.dest.fst 
          from (Sigma.ext_iff.mp hxy).1]) v)
      rw [cast_cast] at this
      exact this
    ), ⟨b, rab, rbc⟩⟩

end Bisim

/-- Bisimilarity setoid for quotienting of SM types -/
def setoid P : Setoid (PreM P) where
  r := Bisim
  iseqv := ⟨Bisim.refl, Bisim.symm, Bisim.trans⟩

@[pp_with_univ]
def uLift (a : PreM.{u, v, w} P) : PreM.{u, v, max x w} P :=
  PreM.corec
    (fun (x : ULift a.β) =>
      have ⟨a, b⟩ := a.gen x.down
      ⟨a, ULift.up ∘ b⟩
    )
    (ULift.up.{x} a.seed)

@[simp]
theorem dest_uLift {a : PreM P}
    : (uLift.{u, v, w, x} a).dest
    = map P uLift a.dest := rfl

end Sme.PreM

end


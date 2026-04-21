import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.PFunctor.Utils
import Mathlib.Control.Functor.Multivariate

open MvFunctor

namespace Sme

universe u v w x y z

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

/-- Preobjects for the SME encoded M-Type -/
@[pp_with_univ]
structure PreM (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) where
  corec ::
  {β : Type v}
  (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
  (g : β)

namespace PreM

set_option trace.Compiler.result true in
/-- Destructor of PreM types -/
@[inline, specialize P]
def dest (x : PreM.{u, v} P α)
    : MvPFunctor.uLift P (TypeVec.uLift.{_, v + 1} α ::: PreM.{u, v} P α) :=
  map (TypeVec.id ::: (PreM.corec x.gen ·.down))
    <| transliterate.{u, v, v+1}
    <| x.gen x.g

@[simp]
theorem dest_corec
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : (corec gen g).dest
    = map (TypeVec.id ::: (corec gen ∘ ULift.down))
      (transliterate.{u,v,v+1} <| gen g) := rfl

/-- Bisimilarity shape for PreM types,
    defined using the new bisim definition. -/
def IsBisim (R : PreM.{u, v} P α → PreM.{u, v} P α → Prop) :=
    ∀ s t, R s t →
      ∃ h : (TypeVec.id ::: Function.const _ PUnit.unit) <$$> s.dest
          = (TypeVec.id ::: Function.const _ PUnit.unit) <$$> t.dest,
      ∀ v, R (s.dest.snd .fz v) (t.dest.snd .fz (cast (by
        have : s.dest.fst = t.dest.fst := (Sigma.ext_iff.mp h).1
        rw [this]
      ) v))

/-- Legacy bisimilarity shape definition -/
def IsBisim.Alt (R : PreM.{u, v} P α → PreM.{u, v} P α → Prop) : Prop :=
    ∀ s t, R s t →
      LiftR (TypeVec.RelLast _ R) s.dest t.dest

theorem IsBisim.Alt_eq
    {R : PreM.{u, v} P α → PreM.{u, v} P α → Prop}
    : IsBisim R = IsBisim.Alt R := propext {
  mpr h s t rst := by
    have ⟨a, fs, ft, hs, ht, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp (h _ _ rst)
    rw! [hs, ht]
    simp only [cast_eq, MvPFunctor.map_mk, exists_prop]
    rw [Sigma.ext_iff]
    simp only [heq_eq_eq, true_and]
    constructor
    · funext i h'
      rcases i with (_|i)
      · rfl
      · exact h i.fs h'
    · exact h .fz
  mp h s t rst := by
    apply (MvPFunctor.liftR_iff _ _ _).mpr
    have ⟨h, hrel⟩ := h _ _ rst
    set t' := t.dest with ht
    rewrite! [←ht] at hrel
    rcases t' with ⟨tf, ts⟩
    obtain ⟨rfl, h⟩ := (Sigma.ext_iff.mp h)
    simp only [MvPFunctor.map_fst, MvPFunctor.map_snd, MvPFunctor.map_mk, heq_eq_eq] at h
    use s.dest.fst
    use s.dest.snd
    use ts
    simp only [Sigma.eta, MvPFunctor.map_fst, true_and]
    rintro (_|i) h'
    · exact hrel h'
    · exact funext_iff.mp (funext_iff.mp h i.fs) h'
}

/-- Bisimilarity of PreM -/
def Bisim : PreM.{u, v} P α → PreM.{u, v} P α → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

namespace Bisim

theorem refl (x : PreM.{u, v} P α) : Bisim x x :=
  ⟨Eq, fun | _, _, .refl _ => ⟨rfl, fun v => rfl⟩, rfl⟩

variable {a b c : PreM.{u, v} P α}

theorem symm (h : Bisim a b) : Bisim b a :=
  have ⟨r, his, rab⟩ := h
  ⟨(fun a b => r b a),
    fun a b h =>
      have ⟨h, hrel⟩ := his _ _ h
      ⟨h.symm, fun v => by
        have := (hrel <| cast (by
          have : b.dest.fst = a.dest.fst := (Sigma.ext_iff.mp h).1
          rw [this]) v)
        rw [cast_cast, cast_eq] at this
        exact this
      ⟩
      , rab⟩

theorem trans (hab : Bisim a b) (hbc : Bisim b c) : Bisim a c :=
  have ⟨r₁, hisAb, rab⟩ := hab
  have ⟨r₂, hisBc, rbc⟩ := hbc
  ⟨(fun a c => ∃ b, r₁ a b ∧ r₂ b c),
    fun | x, z, ⟨y, rxy, ryz⟩ => (by
      have ⟨hxy, hxyrel⟩ := hisAb _ _ rxy
      have ⟨hyz, hyzrel⟩ := hisBc _ _ ryz
      refine ⟨hxy.trans hyz, fun v => ⟨_, (hxyrel v), ?_⟩⟩
      have := (hyzrel <| cast (by 
          have : x.dest.fst = y.dest.fst := (Sigma.ext_iff.mp hxy).1
          rw [this]) v)
      rw [cast_cast] at this
      exact this
    ), ⟨b, rab, rbc⟩⟩

end Bisim

/-- Bisimilarity setoid for quotienting of SM types -/
def setoid (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) : Setoid (PreM P α) where
  r := Bisim
  iseqv := ⟨Bisim.refl, Bisim.symm, Bisim.trans⟩

/-- Lifting of PreM types, lifting the corecursive type -/
@[pp_with_univ, inline]
def uLift (a : PreM.{u, v} P α) : PreM.{u, max v w} P α :=
  .corec (fun x =>
    have v := a.gen x.down
    ⟨
      v.fst.transliterate,
      (.transliterate ::: .up ∘ .transliterate) ⊚ v.snd ⊚ .transliterate
    ⟩
  ) (ULift.up.{w} a.g)

theorem uLift_dest {a : PreM P α} : (uLift.{u,v,w} a).dest =
  ⟨
    ULift.transliterate a.dest.fst,
    (TypeVec.Arrow.transliterate ::: uLift)
    ⊚ a.dest.snd
    ⊚ TypeVec.Arrow.transliterate
  ⟩ := Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl

end Sme.PreM

import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.M.Utils
import Mathlib.Control.Functor.Multivariate

open MvFunctor

namespace Sme

universe u v w x y z

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

@[pp_with_univ]
structure PreM (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) where
  corec ::
  {β : Type v}
  (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
  (g : β)

namespace PreM

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

def IsBisim (R : PreM.{u, v} P α → PreM.{u, v} P α → Prop) : Prop :=
    ∀ s t, R s t →
      LiftR (TypeVec.RelLast _ R) s.dest t.dest

def Bisim : PreM.{u, v} P α → PreM.{u, v} P α → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

namespace Bisim

theorem refl (x : PreM.{u, v} P α) : Bisim x x :=
  ⟨Eq, fun | _, x, .refl _ => (MvPFunctor.liftR_iff _ _ _).mpr <| ⟨
      x.dest.fst, x.dest.snd, x.dest.snd, rfl, rfl,
      fun | .fz, _ | .fs _, _ => rfl
    ⟩, rfl⟩

variable {a b c : PreM.{u, v} P α}

theorem symm (h : Bisim a b) : Bisim b a :=
  have ⟨r, his, rab⟩ := h
  ⟨(fun a b => r b a),
    fun | x, y, rxy => (by
      have ⟨wa, ca, cb, ha, hb, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ rxy
      rw [ha, hb]
      apply (MvPFunctor.liftR_iff _ _ _).mpr
      use wa, cb, ca
      refine ⟨rfl, rfl, ?_⟩
      rintro (_|s) h'
      · exact h .fz h'
      · exact (h (.fs s) h').symm
      ), rab⟩

theorem trans (hab : Bisim a b) (hbc : Bisim b c) : Bisim a c :=
  have ⟨r₁, hisAb, rab⟩ := hab
  have ⟨r₂, hisBc, rbc⟩ := hbc
  ⟨(fun a c => ∃ b, r₁ a b ∧ r₂ b c),
    fun | x, z, rxz => (by
      rcases rxz with ⟨y, rxy, ryz⟩
      have ⟨wa, cx, cy, hx, hy₁, hxy⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| hisAb _ _ rxy
      have ⟨wa', cy', cz, hy₂, hz, hyz⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| hisBc _ _ ryz
      obtain ⟨rfl, rfl⟩ := (Sigma.mk.injEq _ _ _ _).mp <| hy₁.symm.trans hy₂
      rw [hx, hz]
      apply (MvPFunctor.liftR_iff _ _ _).mpr
      use wa, cx, cz
      refine ⟨rfl, rfl, ?_⟩
      rintro (_|s) h'
      · use (cy Fin2.fz h')
        exact ⟨hxy .fz h', hyz .fz h'⟩
      · change _ = _
        exact (hxy (.fs s) h').trans (hyz (.fs s) h')
      ), ⟨b, rab, rbc⟩⟩

end Bisim

def setoid (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) : Setoid (PreM P α) where
  r := Bisim
  iseqv := ⟨Bisim.refl, Bisim.symm, Bisim.trans⟩

@[pp_with_univ]
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

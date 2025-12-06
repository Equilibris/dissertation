import CoinductivePredicates
import Mathlib.Data.Quot
import Mathlib.Tactic.DepRewrite
import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.M.Utils
import Mathlib.Control.Functor.Multivariate

open scoped MvFunctor

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

/- example (x : PreM.{u, v} P α) : True := -/
/-   have := MvFunctor.map (TypeVec.id ::: fun ⟨v⟩ => ULift.up (PreM.corec x.gen v)) <| x.gen x.g -/
/-   sorry -/

def dest (x : PreM.{u, v} P α)
    : MvPFunctor.uLift P (TypeVec.uLift.{_, v + 1} α ::: PreM.{u, v} P α) :=
  MvFunctor.map (TypeVec.id ::: (PreM.corec x.gen ·.down))
    <| transliterate.{u, v, v+1}
    <| x.gen x.g

@[simp]
theorem dest_corec
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : (corec gen g).dest 
    = MvFunctor.map (TypeVec.id ::: (corec gen ∘ ULift.down))
      (transliterate.{u,v,v+1} <| gen g) := rfl

def IsBisim (R : PreM.{u, v} P α → PreM.{u, v} P α → Prop) : Prop :=
    ∀ s t, R s t →
      MvFunctor.LiftR (TypeVec.RelLast _ R) s.dest t.dest

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

end PreM

@[pp_with_univ]
def SM.{args, ind}
    (P : MvPFunctor.{args} (n + 1)) (α : TypeVec.{args} n) :=
  Quotient (PreM.setoid.{args, ind} P α)

namespace SM

def dest : SM.{u, v} P α → MvPFunctor.uLift P (TypeVec.uLift.{_, v + 1} α ::: SM.{u, v} P α) :=
  Quotient.lift (MvFunctor.map (TypeVec.id ::: (Quotient.mk (PreM.setoid P α) ·)) ∘ PreM.dest)
    fun | a, b, ⟨r, his, rab⟩ => (by
      have ⟨hd, ca, cb, ha, hb, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ rab
      dsimp
      rw [ha, hb]
      refine Sigma.ext (by rfl) (heq_of_eq <| funext fun | .fz => ?_ | .fs s => ?_)
      <;> funext h'
      · change ⟦ca Fin2.fz h'⟧ = ⟦cb Fin2.fz h'⟧
        exact Quotient.sound <| ⟨r, his, h .fz h'⟩
      · change ca s.fs h' = cb s.fs h'
        exact (h s.fs h'))

def IsBisim (R : SM.{u, v} P α → SM.{u, v} P α → Prop) : Prop :=
    ∀ s t, R s t →
      MvFunctor.LiftR (TypeVec.RelLast _ R) s.dest t.dest

def Bisim : SM.{u, v} P α → SM.{u, v} P α → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

variable {a b : SM P α}

theorem bisim (h : Bisim a b) : a = b := by
  induction a using Quotient.ind
  induction b using Quotient.ind

  apply Quot.sound

  change PreM.Bisim _ _

  rcases h with ⟨r, his, hhold⟩
  exact ⟨
    fun x y => r (.mk _ x) (.mk _ y),
    fun {x y} hxy => by
      apply (MvPFunctor.liftR_iff _ _ _).mpr
      have ⟨hd, cx, cy, hx, hy, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ hxy
      have ⟨hx'₁, hx'₂⟩ := Sigma.ext_iff.mp hx
      have ⟨hy'₁, hy'₂⟩ := Sigma.ext_iff.mp hy
      dsimp [dest] at hx'₁ hy'₁
      simp [dest] at hx'₂ hy'₂
      use hd
      use cast (by rw [hx'₁]) x.dest.snd
      use cast (by rw [hy'₁]) y.dest.snd
      refine ⟨?_, ?_, ?_⟩
      · rw! (castMode := .all) [←hx'₁]
        apply Sigma.ext (by rfl)
        rfl
      · rw! (castMode := .all) [←hy'₁, ]
        apply Sigma.ext (by rfl)
        rfl
      · rintro (_|s) h'
        · change r _ _
          have hx : @HEq
            (SM P α) (TypeVec.comp (TypeVec.id ::: (⟦·⟧)) x.dest.snd Fin2.fz (Eq.symm (hx'₁) ▸ h'))
            (SM P α) (cx Fin2.fz h') := by
            apply dcongr_heq (by simp)
            · intro a b heq; rfl
            · intro v _
              apply dcongr_heq (by rfl) _ fun v _ => hx'₂
              simp_all
          have hy : @HEq (SM P α)
            (TypeVec.comp (TypeVec.id ::: (⟦·⟧)) y.dest.snd Fin2.fz (Eq.symm (hy'₁) ▸ h'))
            (SM P α) (cy Fin2.fz h') := by
            apply dcongr_heq (by simp)
            · intro a b heq; rfl
            · intro v _
              apply dcongr_heq (by rfl) _ fun v _ => hy'₂
              simp_all
          simp only [TypeVec.comp, TypeVec.appendFun, TypeVec.splitFun, heq_eq_eq] at hx hy
          conv =>
            lhs; rw! (castMode := .all) [←hx'₁]
            change ⟦x.dest.snd Fin2.fz _⟧
            rw [hx]
          conv =>
            rhs; rw! (castMode := .all) [←hy'₁]
            change ⟦y.dest.snd Fin2.fz _⟧
            rw [hy]
          exact h .fz h'
        · change _ = _
          have hx : @HEq
            (ULift (α s)) (@TypeVec.comp _ _ _ (TypeVec.uLift α ::: SM P α)
              (TypeVec.id ::: (⟦·⟧)) x.dest.snd s.fs (cast (by rw [hx'₁]) h'))
            (ULift (α s)) (cx s.fs h') := by
            apply dcongr_heq (by simp)
            · intro a b heq; rfl
            · intro v _
              apply dcongr_heq (by rfl) _ fun v _ => hx'₂
              simp_all
          have hy : @HEq
            (ULift (α s)) (@TypeVec.comp _ _ _ (TypeVec.uLift α ::: SM P α)
              (TypeVec.id ::: (⟦·⟧)) y.dest.snd s.fs (cast (by rw [hy'₁]) h'))
            (ULift (α s)) (cy s.fs h') := by
            apply dcongr_heq (by simp)
            · intro a b heq; rfl
            · intro v _
              apply dcongr_heq (by rfl) _ fun v _ => hy'₂
              simp_all
          simp only [TypeVec.comp, TypeVec.appendFun, TypeVec.splitFun, TypeVec.id,
            heq_eq_eq] at hx hy
          generalize_proofs p₁ p₂
          have h₁ : cast p₁ x.dest.snd s.fs h' = x.dest.snd s.fs (cast (by rw [hx'₁]) h') := by
            clear *-
            apply eq_of_heq
            apply dcongr_heq (cast_heq _ h').symm (fun a b heq => rfl)
            intro a b
            apply dcongr_heq (by rfl)
            · intro a b heq
              rw! [hx'₁, heq]
              rfl
            intro a b
            exact cast_heq p₁ x.dest.snd
          have h₂ : cast p₂ y.dest.snd s.fs h' = y.dest.snd s.fs (cast (by rw [hy'₁]) h' ) := by
            clear *-
            apply eq_of_heq
            apply dcongr_heq (cast_heq _ h').symm (fun a b heq => rfl)
            intro a b
            apply dcongr_heq (by rfl)
            · intro a b heq
              rw! [hy'₁, heq]
              congr!
            intro a b
            exact cast_heq p₂ y.dest.snd
          calc
            _ = _ := h₁
            _ = _ := hx
            _ = _ := h (.fs s) h'
            _ = _ := hy.symm
            _ = _ := h₂.symm
      ,
    hhold
  ⟩

def corec
    {β : Type v}
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : SM P α :=
  .mk _ (.corec gen g)

@[simp]
def dest_corec
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : (corec gen g).dest
    = MvFunctor.map (TypeVec.id ::: (corec gen ∘ ULift.down))
      (transliterate.{u,v,v+1} <| gen g) := by
  dsimp [corec, dest, PreM.dest]
  rw [MvFunctor.map_map, ←TypeVec.appendFun_comp, TypeVec.comp_id]
  rfl

end SM

-- This proof was actually truly pain
def SM.uLift : SM.{u, v} P α → SM.{u, max v w} P α :=
  Quotient.lift (fun a => .mk (PreM.setoid P α) a.uLift)
    fun a b ⟨r, his, hr⟩ =>
      Quot.sound ⟨
        (∃ x y, x.uLift = · ∧ y.uLift = · ∧ r x y),
        by
          rintro _ _ ⟨a,b,rfl,rfl,h⟩
          have ⟨v,f₀,f₁,hx, h, rst⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ h
          obtain ⟨rfl, rfl⟩ := Sigma.ext_iff.mp hx
          have ⟨h₁,h₂⟩ := Sigma.ext_iff.mp h
          clear h hx
          dsimp at h₁ h₂
          rw [PreM.uLift_dest, PreM.uLift_dest]
          rw! (castMode := .all) [h₁, h₂]
          apply (MvPFunctor.liftR_iff _ _ _).mpr
          conv =>
            rhs; intro _; rhs; intro _; rhs; intro _
            rw [Sigma.ext_iff, Sigma.ext_iff]
          dsimp at h₁ h₂ ⊢
          refine ⟨_,_,?_, ⟨rfl, heq_of_eq rfl⟩, ⟨rfl, ?_⟩, ?_⟩
          · refine ?_ ⊚ f₁ ⊚ fun i h => ULift.up h.down
            exact (fun i h => ULift.up h.down) ::: PreM.uLift
          · apply heq_of_eq
            funext i h
            rcases h with ⟨h⟩
            congr! 2
            apply eq_of_heq <| eqRec_heq_iff.mpr <| cast_heq _ f₁
          rintro i ⟨j⟩
          rcases i with (_|i)
          <;> simp [TypeVec.RelLast]
          · exact ⟨_, rfl, _, rfl, rst .fz ⟨j⟩⟩
          · apply ULift.down_inj.mp
            apply ULift.down_inj.mpr
            simp only [TypeVec.comp, TypeVec.appendFun, TypeVec.splitFun,
              TypeVec.Arrow.transliterate, TypeVec.Arrow.uLift_up, TypeVec.Arrow.uLift_down,
              ULift.up.injEq, ULift.down_inj]
            exact rst i.fs ⟨j⟩

          ,
        ⟨_,_,rfl,rfl,hr⟩
      ⟩

end Sme


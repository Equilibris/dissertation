import Mathlib.Data.Quot
import Mathlib.Tactic.DepRewrite
import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.M.Utils
import Sme.M.PreM
import Mathlib.Control.Functor.Multivariate

open MvFunctor

namespace Sme

universe u v w x y z

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

@[pp_with_univ]
def SM.{args, ind}
    (P : MvPFunctor.{args} (n + 1)) (α : TypeVec.{args} n) :=
  Quotient (PreM.setoid.{args, ind} P α)

namespace SM

set_option trace.compiler.ir.result true in
@[inline, specialize n P α]
def dest : SM.{u, v} P α → MvPFunctor.uLift P (TypeVec.uLift.{_, v + 1} α ::: SM.{u, v} P α) :=
  Quotient.lift (map (TypeVec.id ::: (Quotient.mk (PreM.setoid P α) ·)) ∘ PreM.dest)
    fun | a, b, ⟨r, his, rab⟩ => (by
      have ⟨hd, ca, cb, ha, hb, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ rab
      dsimp
      rw [ha, hb]
      refine Sigma.ext rfl (heq_of_eq <| funext fun | .fz => ?_ | .fs s => ?_)
      <;> funext h'
      · change ⟦ca Fin2.fz h'⟧ = ⟦cb Fin2.fz h'⟧
        exact Quotient.sound <| ⟨r, his, h .fz h'⟩
      · change ca s.fs h' = cb s.fs h'
        exact (h s.fs h'))

def IsBisim (R : SM.{u, v} P α → SM.{u, v} P α → Prop) : Prop :=
    ∀ s t, R s t →
      LiftR (TypeVec.RelLast _ R) s.dest t.dest

def Bisim : SM.{u, v} P α → SM.{u, v} P α → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

variable {a b : SM P α}

theorem bisim (h : Bisim a b) : a = b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  --
  apply Quot.sound
  change PreM.Bisim _ _
  --
  rcases h with ⟨r, his, hhold⟩
  exact ⟨
    fun x y => r (.mk _ x) (.mk _ y),
    fun {x y} hxy => by
      apply (MvPFunctor.liftR_iff _ _ _).mpr
      have ⟨hd, cx, cy, hx, hy, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ hxy
      have ⟨hx'₁, hx'₂⟩ := Sigma.ext_iff.mp hx
      have ⟨hy'₁, hy'₂⟩ := Sigma.ext_iff.mp hy
      dsimp [dest] at hx'₁ hy'₁
      simp only [dest, Quotient.lift_mk, Function.comp_apply, MvPFunctor.map_fst, 
        MvPFunctor.map_snd] at hx'₂ hy'₂
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
          rw! (castMode := .all) [←hx'₁]
          dsimp
          rw [hx]
          rw! (castMode := .all) [hx'₁, ←hy'₁]
          dsimp
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
theorem dest_corec
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : (corec gen g).dest
    = map (TypeVec.id ::: (corec gen ∘ ULift.down))
      (transliterate.{u,v,v+1} <| gen g) := by
  dsimp [corec, dest, PreM.dest]
  rw [map_map, ←TypeVec.appendFun_comp, TypeVec.comp_id]
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
          <;> simp only [exists_and_left, TypeVec.comp.get, TypeVec.append1_get_fz,
            TypeVec.appendFun.get_fz, Function.comp_apply, exists_and_left, TypeVec.comp.get,
            TypeVec.append1_get_fs, TypeVec.appendFun.get_fs, Function.comp_apply]
          · exact ⟨_, rfl, _, rfl, rst .fz ⟨j⟩⟩
          · apply ULift.down_inj.mp
            apply ULift.down_inj.mpr
            simp only [TypeVec.Arrow.transliterate, TypeVec.comp, TypeVec.Arrow.uLift_up,
              TypeVec.Arrow.uLift_down, ULift.up.injEq, ULift.down_inj]
            exact rst i.fs ⟨j⟩
          ,
        ⟨_,_,rfl,rfl,hr⟩
      ⟩

end Sme


import Mathlib.Data.Quot
import Mathlib.Tactic.DepRewrite
import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.PFunctor.Utils
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

set_option trace.Compiler.result true in
@[inline, specialize P n]
def dest : SM.{u, v} P α → MvPFunctor.uLift P (TypeVec.uLift.{_, v + 1} α ::: SM.{u, v} P α) :=
  Quotient.lift (map (TypeVec.id ::: (Quotient.mk (PreM.setoid P α) ·)) ∘ PreM.dest)
    fun | a, b, ⟨r, his, rab⟩ => (by
      rw [PreM.IsBisim.Alt_eq] at his
      have ⟨hd, ca, cb, ha, hb, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ rab
      dsimp
      rw [ha, hb]
      refine Sigma.ext rfl (heq_of_eq <| funext₂ fun | .fz, h' | .fs s, h' => ?_)
      · change ⟦ca Fin2.fz h'⟧ = ⟦cb Fin2.fz h'⟧
        exact Quotient.sound <| ⟨r, PreM.IsBisim.Alt_eq ▸ his, h .fz h'⟩
      · change ca s.fs h' = cb s.fs h'
        exact (h s.fs h'))

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


def IsBisim (R : SM.{u, v} P α → SM.{u, v} P α → Prop) : Prop :=
    ∀ s t, R s t →
      LiftR (TypeVec.RelLast _ R) s.dest t.dest

def IsBisim.Alt (R : SM.{u, v} P α → SM.{u, v} P α → Prop) :=
    ∀ s t, R s t →
      ∃ h : (TypeVec.id ::: Function.const _ PUnit.unit) <$$> s.dest
          = (TypeVec.id ::: Function.const _ PUnit.unit) <$$> t.dest,
      ∀ v, R (s.dest.snd .fz v) (t.dest.snd .fz (cast (by
        generalize s.dest = s, t.dest = t at h ⊢
        rcases s with ⟨sf, _⟩
        rcases t with ⟨tf, _⟩
        obtain ⟨rfl, -⟩ := Sigma.ext_iff.mp h
        rfl
      ) v))

theorem IsBisim.Alt_eq
    {R : SM.{u, v} P α → SM.{u, v} P α → Prop}
    : IsBisim R = IsBisim.Alt R := propext {
  mp h s t rst := by
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
  mpr h s t rst := by
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


def Bisim : SM.{u, v} P α → SM.{u, v} P α → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

variable {a b : SM P α}

theorem bisim (h : Bisim a b) : a = b := by
  cases a, b using Quotient.ind₂
  apply Quot.sound
  change PreM.Bisim _ _
  rcases h with ⟨r, his, hhold⟩
  refine ⟨fun x y => r (.mk _ x) (.mk _ y), ?_ , hhold⟩
  clear *-his
  intro s t rst
  have ⟨hm, h⟩ := IsBisim.Alt_eq.mp his _ _ rst
  dsimp [dest] at hm h
  rw [MvFunctor.map_map, MvFunctor.map_map, TypeVec.appendFun_comp'] at hm
  exact ⟨hm, h⟩

-- This proof was actually truly pain
def uLift : SM.{u, v} P α → SM.{u, max v w} P α :=
  Quotient.lift (fun a => .mk (PreM.setoid P α) a.uLift)
    fun a b ⟨r, his, hr⟩ =>
      Quot.sound ⟨
        (∃ x y, x.uLift = · ∧ y.uLift = · ∧ r x y),
        by
          /- clear *-his hr -/
          /- rintro _ _ ⟨a,b,rfl,rfl,h⟩ -/
          /- have ⟨h, hrel⟩ := his _ _ hr -/
          /- refine ⟨?_, ?_⟩ -/
          /- · simp only [PreM.uLift, ULift.transliterate_down, PreM.dest_corec, transliterate, -/
          /-     transliterateMap, map_map, TypeVec.appendFun_comp', TypeVec.comp_id, -/
          /-     Function.const_comp] -/
          /-   change Sigma.mk _ _ = Sigma.mk _ _ -/
          /-   simp [← TypeVec.comp_assoc, TypeVec.appendFun_comp', transliterate, transliterateMap] -/
          /-   sorry -/
          /- intro ⟨v⟩ -/
          /- dsimp [PreM.uLift] at v -/
          /- refine ⟨_, ?_, ?_, hrel <| .up v⟩ -/
          /- simp -/
          /- stop -/
          rw [PreM.IsBisim.Alt_eq] at his ⊢
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
            exact rst i.fs ⟨j⟩,
        ⟨_,_,rfl,rfl,hr⟩
      ⟩

end Sme.SM


import Mathlib.Data.Quot
import Mathlib.Tactic.DepRewrite
import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.UniM.PreM
import Mathlib.Control.Functor.Multivariate

open PFunctor

namespace Sme

universe u v w x y z

variable {P : PFunctor.{u, v}}

@[pp_with_univ]
def SM (P : PFunctor.{u, v}) :=
  Quotient (PreM.setoid.{u, v, w} P)

namespace SM

def dest : SM P → P (SM.{u, v, w} P) :=
  Quotient.lift
    (map _ (Quotient.mk _) ∘ PreM.dest)
    <| by
      rintro ⟨af, as⟩ ⟨bf, bs⟩ ⟨r, ibr, hr⟩
      have ⟨h, rest⟩ := ibr _ _ hr
      have : Sigma.fst (af as) = Sigma.fst (bf bs) := (Sigma.ext_iff.mp h).1
      dsimp at rest ⊢
      generalize h1 : af as = a, h2: bf bs = b at this
      rcases a with ⟨ax, afam⟩
      rcases b with ⟨bx, bfam⟩
      subst this
      dsimp at *
      refine Sigma.ext rfl <| heq_of_eq <| funext fun i => Quot.sound ⟨r, ibr, ?_⟩
      have := rest <| cast (by simp [h1]) i
      simp only [cast_cast] at this
      rewrite! [h1, h2] at this
      exact this

@[inline]
def corec
    {β : Type w}
    (gen : β → P β)
    (seed : β)
    : SM P :=
  .mk _ (.corec gen seed)


@[simp]
theorem dest_corec
    {β : Type w}
    (gen : β → P β)
    (seed : β)
    : (corec gen seed).dest
    = map _ (corec gen) (gen seed) :=
  rfl

def IsBisim (R : SM.{u, v, w} P → SM.{u, v, w} P → Prop) :=
    ∀ s t, R s t →
      ∃ h : (Function.const _ PUnit.unit) <$> s.dest
          = (Function.const _ PUnit.unit) <$> t.dest,
      ∀ v, R (s.dest.snd v) (t.dest.snd (cast (by
        rw [show s.dest.fst = t.dest.fst from (Sigma.ext_iff.mp h).1]
      ) v))

def Bisim : SM.{u, v, w} P → SM.{u, v, w} P → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

variable {a b : SM P}

theorem bisim : Bisim a b → a = b := by
  rcases a with ⟨agen, bseed⟩
  rcases b with ⟨agen, bseed⟩
  exact fun ⟨r, his, hhold⟩ =>
    Quot.sound ⟨(fun a b => r (.mk _ a) (.mk _ b)), fun _ _ => his _ _, hhold⟩

def uLift : SM.{u, v, w} P → SM.{u, v, max w x} P :=
  Quotient.lift
    (.mk _ ∘ PreM.uLift)
    <| by
      intro a b ⟨r, rib, rab⟩
      dsimp
      refine Quot.sound ⟨fun a b =>
        ∃ x y, a = PreM.uLift.{u, v, w, x} x
          ∧ b = PreM.uLift.{u, v, w, x} y
          ∧ r x y,
        ?_,
        ⟨_, _, rfl, rfl, rab⟩⟩
      rintro s t ⟨x, y, rfl, rfl, rxy⟩
      dsimp [PreM.dest_uLift]
      rw! [P.map_map, P.map_map]
      have ⟨hf, hrst⟩ := rib _ _ rxy
      dsimp
      have : P.map 
          (Function.const (PreM.{u, v, w} P) PUnit.unit.{(max u v ((max w x) + 1)) + 1}) x.dest
        = P.map (Function.const (PreM.{u, v, w} P) PUnit.unit) y.dest := by
        dsimp [] at hf
        change P.map ((Function.const _ PUnit.unit.{(max (max u v) ((max w x) + 1)) + 1})
          ∘ (Function.const _ PUnit.unit.{(max (max u v) (w + 1)) + 1})) x.dest = _
        rw [←P.map_map, hf]
        rfl
      refine ⟨this, ?_⟩
      · intro v
        refine ⟨
          x.dest.snd v,
          y.dest.snd <| cast (by
            rw [←show x.dest.fst = y.dest.fst from (Sigma.ext_iff.mp this).1]
            rfl) v,
          rfl,
          rfl,
          hrst v⟩

@[simp]
theorem dest_uList
    (x : SM.{u, v, w} P)
    : (uLift.{_, _, _, x} x).dest
    = map P uLift x.dest := by
  rcases x with ⟨x⟩
  dsimp [uLift, dest]
  rw [P.map_map, P.map_map]
  rfl


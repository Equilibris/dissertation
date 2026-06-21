import Sme.AltRepr
import Sme.HEq
import Sme.UniM.Equiv
import Mathlib.Logic.Small.Defs

open PFunctor

namespace Sme.Uni

universe u v w x

variable {n : Nat} {P : PFunctor.{u, v}}

open SM

@[pp_with_univ]
def equivXU : SM.{u, v, max u v w} P ≃ SM.{u, v, max u v x} P :=
  equivP.trans equivP.symm

namespace equivXU

theorem inv'
    {x : SM.{u, v, max u v w} P}
    : equivXU x = x := by
  simp [equivXU]

theorem contract'
    {x : SM.{u, v, max u v w} P}
    : (equivXU ∘ equivXU) x = equivXU x := by
  simp [equivXU]

theorem toFun_invFun'
    {x : SM.{u, v, max u v w} P}
    : equivXU x = equivXU.symm x := by
  simp [equivXU]

def transform
    (v : P (SM.{u, v, max u v w} P))
    : P (SM.{u, v, max u v x} P) where
  fst := v.fst
  snd := equivXU ∘ v.snd

end equivXU


@[simp]
theorem transform_dest
    {x : SM.{u, v, max u v w} P}
    : (equivXU.{u, v, w} x).dest = equivXU.transform (dest x) := rfl

@[inline]
private unsafe def equivXUImpl : SM.{u, v, max u v w} P ≃ SM.{u, v, max u v x} P where
  toFun := unsafeCast
  invFun := unsafeCast
  left_inv _ := lcProof
  right_inv _ := lcProof

attribute [irreducible, implemented_by equivXUImpl, inline] equivXU

def M (P : PFunctor.{u, v}) : Type max u v :=
  AltRepr P.M (SM.{u,v, max u v} P) equivP.symm

namespace M

def corec
    {β : Type w}
    (gen : β → P β)
    (g : β)
    : M P :=
  .mkB
    <| (equivXU.{u, v, max u v w, max u v}).toFun
    <| SM.uLift.{u, v, w, max u v}
    <| .corec gen g

def dest : M.{u, v} P → P (M.{u, v} P) :=
  AltRepr.rec
    (AltRepr.mkA <$> PFunctor.M.dest ·)
    (PFunctor.map P .mkB ·.dest)
    (fun _ =>
      heq_of_eq <| Sigma.ext rfl <| heq_of_eq <| funext fun _ =>
        AltRepr.mkA_mkB_iff_eq.mpr rfl)
    (fun _ =>
      heq_of_eq <| Sigma.ext rfl <| heq_of_eq <| funext fun _ =>
        Eq.symm <| AltRepr.mkA_mkB_iff_eq_symm.mpr rfl)

@[simp]
theorem dest_corec
    {β : Type w}
    (gen : β → P β)
    (g : β)
    : dest (corec gen g)
    = PFunctor.map P (corec gen) (gen g)
    := by
  simp [dest, corec]
  rfl

def head : M P → P.A := Sigma.fst ∘ M.dest
def children (x : M P) : P.B (head x) → M P :=
  Sigma.snd x.dest

@[simp]
theorem head_children_eta {x : M P}
    : ⟨x.head, x.children⟩ = x.dest := rfl

section bisim

def IsBisim (R : M.{u, v} P → M.{u, v} P → Prop) : Prop :=
    ∀ s t, R s t →
      ∃ h : PFunctor.map P (Function.const _ PUnit.unit.{max u v + 1}) s.dest
          = PFunctor.map P (Function.const _ PUnit.unit.{max u v + 1}) t.dest,
      ∀ v, R (s.dest.snd v) (t.dest.snd (cast (by
        rw [show s.dest.fst = t.dest.fst from (Sigma.ext_iff.mp h).1]
      ) v))
        /- MvFunctor.LiftR (TypeVec.RelLast _ R) s.dest t.dest -/

def Bisim : M.{u, v} P → M.{u, v} P → Prop := (∃ R, IsBisim R ∧ R · ·)

theorem bisim' {a b : M.{u, v} P} : Bisim a b → a = b := by
  intro ⟨r, ris, rab⟩
  apply a.extB
  rintro a b rfl rfl
  refine SM.bisim ⟨(fun a b => r (.mkB a) (.mkB b)), ?_, rab⟩
  clear a b rab; intro a b rab
  have ⟨h, hrst⟩ := ris _ _ rab
  simp only [dest, map_eq_map, AltRepr.recCheap, PFunctor.map_map, Function.const_comp] at h
  constructor
  case w =>
    change P.map (Function.const _ PUnit.unit ∘ Function.const _ PUnit.unit.{max u v +1}) a.dest = _
    rw [←PFunctor.map_map, h]
    rfl
  · intro v
    specialize hrst (cast (by simp [dest]) v)
    simp only [dest, map_eq_map, cast_cast] at hrst
    rewrite! [AltRepr.recCheap] at hrst
    generalize_proofs at hrst
    rewrite! [AltRepr.recCheap] at hrst
    exact hrst

theorem bisim
    {a b : M.{u, v} P}
    (R : M.{u, v} P → M.{u, v} P → Prop)
    (x : R a b)
    (h : ∀ s t, R s t →
      ∃ h : PFunctor.map P (Function.const _ PUnit.unit.{max u v + 1}) s.dest
          = PFunctor.map P (Function.const _ PUnit.unit.{max u v + 1}) t.dest,
      ∀ v, R (s.dest.snd v) (t.dest.snd (cast (by
        rw [show s.dest.fst = t.dest.fst from (Sigma.ext_iff.mp h).1]) v)))
    : a = b :=
  bisim' ⟨R, fun s t h' => h s t h', x⟩

@[specialize P]
def mk : P (M P) → M P :=
  corec (P.map dest ·)

@[simp]
theorem dest_mk {v : M P} : mk (dest v) = v := by
  apply bisim (· = (mk ∘ dest) ·) rfl
  rintro _ x rfl
  dsimp [mk]
  rw! [dest_corec]
  simp only [cast_eq, PFunctor.map_map, Function.const_comp, exists_const]
  exact fun v => rfl

@[elab_as_elim]
theorem mk_cases {motive : M P → Prop}
    (h : ∀ v, motive (.mk v)) v : motive v := by
  rw [←dest_mk (v := v)]
  exact h v.dest

@[simp]
theorem mk_dest {v : P (M P)} : dest (mk v) = v := by
  rw [mk, dest_corec, ←mk, PFunctor.map_map,
    show mk ∘ dest = @id (M P) from funext fun x => dest_mk]
  rfl

theorem mk_linv : Function.LeftInverse dest (mk (P := P)) :=
  fun _ => mk_dest
theorem dest_linv : Function.LeftInverse (mk (P := P)) dest :=
  fun _ => dest_mk

theorem mk.bij : Function.Bijective (mk (P := P)) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    dest,
    mk_linv,
    dest_linv,
  ⟩

theorem dest.bij : Function.Bijective (dest (P := P)) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    mk,
    dest_linv,
    mk_linv,
  ⟩

theorem mk.inj : Function.Injective     (mk (P := P))   := mk.bij.injective
theorem mk.sur : Function.Surjective    (mk (P := P))   := mk.bij.surjective
theorem dest.inj : Function.Injective   (dest (P := P)) := dest.bij.injective
theorem dest.sur : Function.Surjective  (dest (P := P)) := dest.bij.surjective

@[ext 1000]
theorem ext_dest {x y : M P} (h : x.dest = y.dest) : x = y := by
  rw [← dest_mk (v := x), h, dest_mk]

/- @[ext 0] -/
theorem ext_mk
    {x y : P (M P)}
    (h : mk x = mk y)
    : x = y := by
  rw [← mk_dest (v := x), h, mk_dest]

instance inhabited
    [I : Inhabited P.A]
    : Inhabited (M P) where
  default := .corec (fun x => ⟨x, fun _ => x⟩) I.default

end bisim

end Sme.Uni.M

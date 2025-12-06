import Sme.M.SDefs
import Sme.ABI
import Sme.M.Utils
import Mathlib.Logic.Small.Defs

open scoped MvFunctor
open MvPFunctor

namespace Sme

universe u v w

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n}

def SM.equivP : SM.{u, max u v} P α ≃ M.{u} P α :=
  let msm := (MvFunctor.map (TypeVec.id ::: ULift.up.{u, max u v + 1}) ∘ SM.dest)
  let mpa := liftAppend.{u, max u v} ∘ M.dest P ∘ ULift.down.{max u v, u}
  ⟨
    .corecU P msm,
    .corec mpa ∘ ULift.up,
    fun x => SM.bisim ⟨
      (· = (.corec mpa ∘ ULift.up ∘ .corecU _ msm) ·),
      fun a b => by
        rcases b with ⟨⟨gen, g⟩⟩
        rintro rfl
        exact (MvPFunctor.liftR_iff _ _ _).mpr ⟨
          .up (gen g).fst.down,
          fun
            | .fz, h => .corec mpa
              <| ULift.up
              <| M.corecU P msm
              <| corec gen (((gen g).snd Fin2.fz ∘ ULift.up) h.down).down
            | .fs s, .up h => (gen g).snd (.fs s) (.up h) |>.down |> .up,
          fun
            | .fz, h  => .corec gen ((gen g).snd .fz (.up h.down)).down
            | .fs s, h => (gen g).snd (.fs s) (.up h.down) |>.down |> .up,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
          fun | .fz, h | .fs _, h => rfl,
        ⟩,
      rfl
    ⟩,
    fun x => M.bisim _
      (· = (.corecU _ msm ∘ .corec mpa ∘ .up) ·)
      (fun a b => (· ▸ ⟨
        (corec mpa <| .up b).dest.fst.down,
        ((M.dest P b).snd ·.fs),
        (M.corecU P msm <| (corec mpa <| .up b).dest.snd Fin2.fz <|.up ·),
        (M.dest P b).snd .fz,
        Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => rfl,
        Sigma.ext rfl <| heq_of_eq rfl,
        fun _ => rfl
      ⟩))
      _ _
      rfl,
  ⟩

section

@[pp_with_univ]
def SM.equivXU : SM.{u, max u v} P α ≃ SM.{u, max u w} P α :=
  SM.equivP.trans SM.equivP.symm

theorem SM.equivXU.inv'
    {x : SM.{u, max u v} P α}
    : SM.equivXU x = x := by
  simp [SM.equivXU]

theorem SM.equivXU.contract'
    {x : SM.{u, max u v} P α}
    : (SM.equivXU ∘ SM.equivXU) x = SM.equivXU x := by
  simp [SM.equivXU]

theorem SM.equivXU.toFun_invFun'
    {x : SM.{u, max u v} P α}
    : SM.equivXU x = SM.equivXU.symm x := by
  simp [SM.equivXU]

def SM.equivXU.transform
    (v : (MvPFunctor.uLift.{u, (max u w) + 1} P)
      (TypeVec.uLift.{u, (max u w) + 1} α ::: SM.{u, max u w} P α))
    : (MvPFunctor.uLift.{u, (max u v) + 1} P) 
      (TypeVec.uLift.{u, (max u v) + 1} α ::: SM.{u, max u v} P α) :=
  ⟨
    .up v.fst.down,
    fun
      | .fz, h => SM.equivXU (v.snd .fz (.up h.down))
      | .fs s, h => .up (v.snd (s.fs) (.up h.down)).down
  ⟩

@[simp]
theorem SM.transform_dest
    {x : SM.{u, max u v} P α}
    : (SM.equivXU.{u, v, w} x).dest = SM.equivXU.transform (SM.dest x) := by
  dsimp [equivXU, equivP]
  simp [SM.dest_corec]
  refine Sigma.ext (by rfl) <| heq_of_eq ?_
  funext i h
  rcases i with (_|⟨s⟩)
  · rfl
  · rfl

-- The soundness of this is extremely dubious
private unsafe def SM.equivXUImpl : SM.{u, max u v} P α ≃ SM.{u, max u w} P α where
  toFun := unsafeCast
  invFun := unsafeCast
  left_inv _ := lcProof
  right_inv _ := lcProof

attribute [irreducible, implemented_by SM.equivXUImpl] SM.equivXU

end

/-- info: 'Sme.SM.equivP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SM.equivP

def HpLuM (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) : Type u :=
  ABI _ _ (SM.equivP.{u, u} (P := P) (α := α)).symm

namespace HpLuM

def corec
    {β : Type v}
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : HpLuM P α :=
  .mkB <| SM.equivXU <| SM.uLift.{u, v, max u v} <| .corec gen g

def dest : HpLuM P α → P (α ::: HpLuM P α) :=
  ABI.rec
    ((TypeVec.id ::: ABI.mkA) <$$> M.dest P ·)
    (MvPFunctor.uLift_down
      <| (.mp TypeVec.uLift_append1_ULift_uLift ⊚ (TypeVec.id ::: .up ∘ .mkB)) <$$> ·.dest)
    (fun _ =>
      heq_of_eq <| Sigma.ext rfl <| heq_of_eq <| funext fun
        | .fz => funext fun _ => ABI.mkA_mkB_iff_eq.mpr rfl
        | .fs _ => rfl)
    (fun _ =>
      heq_of_eq <| Sigma.ext rfl <| heq_of_eq <| funext fun
        | .fz => funext fun _ => Eq.symm <| ABI.mkA_mkB_iff_eq_symm.mpr rfl
        | .fs _ => rfl)

@[simp]
theorem dest_corec
    {β : Type v}
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : dest (corec gen g) =
      uLift_down (
        ((.mp TypeVec.uLift_append1_ULift_uLift ⊚ (TypeVec.id ::: .up ∘ corec gen ∘ ULift.down)))
        <$$> gen g
      ) := by
  simp only [dest, uLift_down, map_fst, map_snd, corec, ABI.recCheap]
  rw [SM.transform_dest]
  refine Sigma.ext (by rfl) <| heq_of_eq <| funext fun | .fz | .fs _ => rfl

def IsBisim (R : HpLuM.{u} P α → HpLuM.{u} P α → Prop) : Prop :=
    ∀ s t, R s t → MvFunctor.LiftR (TypeVec.RelLast _ R) s.dest t.dest

def Bisim : HpLuM.{u} P α → HpLuM.{u} P α → Prop := (∃ R, IsBisim R ∧ R · ·)

theorem castFn
    {A : Type u} {B C : A → Type v}
    {eq : ((v : A) → B v) = ((v : A) → C v)}
    {v : ((v : A) → B v)}
    (eq₂ : ∀ z, B z = C z) {z}
    : (cast eq v) z = cast (eq₂ z) (v z) := by
  apply eq_of_heq
  refine (heq_cast_iff_heq _ _ _).mpr ?_
  apply dcongr_heq (by rfl)
  · rintro x _ rfl; exact (eq₂ x).symm
  intro _ _
  exact cast_heq eq v

theorem castFn'
    {A A' : Type u} {B : A → Type v} {C : A' → Type v}
    {eq : ((v : A) → B v) = ((v : A') → C v)}
    {v : ((v : A) → B v)}
    (eq₂ : A' = A)
    (eq₃ : ∀ a b, a ≍ b → B a = C b) {z}
    : (cast eq v) z = cast (eq₃ _ _ (cast_heq eq₂ z)) (v (cast eq₂ z)) := by
  apply eq_of_heq
  refine (heq_cast_iff_heq _ _ _).mpr ?_
  apply dcongr_heq
  · exact (cast_heq eq₂ z).symm
  · exact fun _ _ heq => (eq₃ _ _ (HEq.symm heq)).symm
  intro _ _
  exact cast_heq eq v

theorem bisim {a b : HpLuM.{u} P α} : Bisim a b → a = b := by
  intro ⟨r, ris, rab⟩
  apply a.extB
  intro a b rfl rfl
  refine SM.bisim ⟨(fun a b => r (.mkB a) (.mkB b)), ?_, rab⟩
  clear a b rab; intro a b rab
  have := (MvPFunctor.liftR_iff _ _ _).mp <| ris (.mkB a) (.mkB b) rab
  simp only [dest, ABI.recCheap] at this
  rcases this with ⟨a,f₀,f₁, ha, hb, rst⟩; rcases ha
  have ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.mp hb
  simp only [map_fst, ULift.down_inj, TypeVec.Arrow.uLift_arrow, map_snd] at h₁ h₂; clear hb
  apply (MvPFunctor.liftR_iff _ _ _).mpr
  conv =>
    rhs; intro _; rhs; intro _; rhs; intro _
    rw [Sigma.ext_iff, Sigma.ext_iff]
  dsimp only
  refine ⟨_, _, ?_, ⟨rfl, heq_of_eq rfl⟩, ⟨h₁, ?_⟩, ?_⟩
  · exact (TypeVec.Arrow.uLift_up.{u, u + 1} ::: ABI.destB)
      ⊚ f₁
      ⊚ TypeVec.Arrow.uLift_down.{u, u + 1}
  · rw! [←h₂]
    apply Function.hfunext rfl
    rintro i _ rfl
    apply Function.hfunext
    · rw [h₁]
    intro x y heq
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    have heq' : x ≍ y := by
      rw [←ULift.down_up x, ←ULift.down_up y]
      rw! [heq]
      congr 3
      exact cast_heq _ _
    clear heq
    rw! [←heq']
    rcases i with (_|i)
    <;> simp only [TypeVec.append1_get_fs, map_fst, TypeVec.comp.get, TypeVec.appendFun.get_fs,
      TypeVec.Arrow.uLift_up, TypeVec.uLift_down.get, Function.comp_apply, heq_eq_eq,
      TypeVec.append1_get_fz, TypeVec.appendFun.get_fz]
    <;> rw [castFn (fun _ => by rw [h₁])]
    <;> simp only [TypeVec.append1_get_fz, TypeVec.comp.get, TypeVec.uLift_down.get,
      TypeVec.appendFun.get_fz, TypeVec.uLift_up.get,
      TypeVec.append1_get_fs, TypeVec.appendFun.get_fs]
    <;> rw [castFn' (by rw [h₁]) fun _ _ _ => by rfl]
    <;> simp only [TypeVec.append1_get_fz, TypeVec.Arrow.mp, eq_mp_eq_cast, cast_cast, cast_eq,
      Function.comp_apply, ABI.mkB_destB']
    · rfl
  · intro i ⟨h⟩
    specialize rst i h
    rcases i with (_|i)
    · simp only [TypeVec.RelLast, map_fst, TypeVec.comp.get, TypeVec.append1_get_fz,
        TypeVec.appendFun.get_fz, TypeVec.uLift_down.get, Function.comp_apply, ABI.destB_mkB']
      exact rst
    · exact ULift.down_inj.mp rst

end HpLuM

end Sme

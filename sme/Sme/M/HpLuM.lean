import Sme.ABI
import Sme.HEq
import Sme.M.Equiv
import Mathlib.Logic.Small.Defs

open scoped MvFunctor
open MvPFunctor

namespace Sme

universe u v w

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n}

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

section bisim

def IsBisim (R : HpLuM.{u} P α → HpLuM.{u} P α → Prop) : Prop :=
    ∀ s t, R s t → MvFunctor.LiftR (TypeVec.RelLast _ R) s.dest t.dest

def Bisim : HpLuM.{u} P α → HpLuM.{u} P α → Prop := (∃ R, IsBisim R ∧ R · ·)

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
    <;> rw [dcastFn (by rw [h₁]) fun _ _ _ => by rfl]
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

end bisim

def corec'
    {β : Type u}
    (gen : β → P (α ::: β))
    : β → HpLuM P α :=
  corec (fun v => .mpr TypeVec.uLift_append1_ULift_uLift <$$> uLift_up.{u,u} (gen v))

def mk : P (α ::: HpLuM P α) → HpLuM P α :=
  corec' ((TypeVec.id ::: dest) <$$> ·)

@[simp]
theorem dest_corec'
    {β : Type u}
    (gen : β → P (α ::: β))
    (g : β)
    : dest (corec' gen g) =
      (TypeVec.id ::: corec' gen) <$$> gen g
     := by
  dsimp [corec']
  rw [dest_corec]
  refine Sigma.ext (by rfl) <| heq_of_eq ?_
  funext i h
  rcases i with (_|i) <;> rfl

theorem dest_mk {v : HpLuM P α} : mk (dest v) = v := by
  refine bisim ⟨(· = (mk ∘ dest) ·), ?_, rfl⟩
  rintro _ x rfl
  dsimp [mk]
  rw [dest_corec']
  apply (MvPFunctor.liftR_iff _ _ _).mpr
  conv =>
    rhs; intro _; rhs; intro _; rhs; intro _
    rw [Sigma.ext_iff, Sigma.ext_iff]
  dsimp
  refine ⟨_, _, _, ⟨rfl, heq_of_eq rfl⟩, ⟨rfl, (heq_of_eq rfl)⟩, ?_⟩
  rintro (_|i) h <;> rfl

theorem mk_dest {v : P (α ::: HpLuM P α)} : dest (mk v) = v := by
  have : mk ∘ dest = @_root_.id (HpLuM P α) := funext fun x => dest_mk
  rw [mk, dest_corec', ←mk, ←comp_map]
  refine Sigma.ext (by rfl) <| heq_of_eq ?_
  dsimp only [map_fst, map_snd]
  funext i h
  rcases i with (_|i)
  · change (mk ∘ dest) _ = id _
    rw [this]
  · rfl

def map {α β : TypeVec.{u} n} (m : α ⟹ β) : HpLuM P α → HpLuM P β :=
  corec' ((m ::: id) <$$> ·.dest)

instance : MvFunctor (HpLuM P) where map := map

theorem id_map (x : HpLuM P α) : TypeVec.id <$$> x = x := by
  apply bisim ⟨(· = TypeVec.id <$$> ·), ?_, rfl⟩
  intro _ y rfl
  change MvFunctor.LiftR _ (corec' _ _).dest y.dest
  rw [dest_corec']
  apply (MvPFunctor.liftR_iff _ _ _).mpr
  conv =>
    rhs; intro _; rhs; intro _; rhs; intro _
    rw [Sigma.ext_iff, Sigma.ext_iff]
  refine ⟨_, _, _, ⟨rfl, heq_of_eq rfl⟩, ⟨rfl, (heq_of_eq rfl)⟩, ?_⟩
  rintro (_|i) h <;> rfl

theorem comp_map
    {α β γ}
    (g : α ⟹ β) (h : β ⟹ γ)
    (x : HpLuM P α)
    : (h ⊚ g) <$$> x = h <$$> g <$$> x := by
  apply bisim ⟨(fun a b => ∃ y, a = (h ⊚ g) <$$> y ∧ b = h <$$> g <$$> y), ?ib, ⟨x, rfl, rfl⟩⟩
  rintro a b ⟨y, rfl, rfl⟩
  change MvFunctor.LiftR _ (corec' _ y).dest (corec' _ (corec' _ y)).dest
  rw [dest_corec', dest_corec', dest_corec']
  apply (MvPFunctor.liftR_iff _ _ _).mpr
  conv =>
    rhs; intro _; rhs; intro _; rhs; intro _
    rw [Sigma.ext_iff, Sigma.ext_iff]
  refine ⟨_, _, _, ⟨rfl, heq_of_eq rfl⟩, ⟨rfl, heq_of_eq rfl⟩, ?_⟩
  rintro (_|i) h
  · refine ⟨_, rfl, rfl⟩
  · rfl

instance : LawfulMvFunctor (HpLuM P) where
  id_map := id_map
  comp_map := comp_map

end Sme.HpLuM


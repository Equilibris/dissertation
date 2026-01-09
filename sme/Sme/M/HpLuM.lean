import Sme.ABI
import Sme.HEq
import Sme.M.Equiv
import Sme.PFunctor.EquivP
import Sme.PFunctor.NatIso
import Mathlib.Logic.Small.Defs

open scoped MvFunctor
open MvPFunctor

namespace Sme

universe u v w

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n}

def HpLuM (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) : Type u :=
  ABI _ _ (SM.equivP.{u, u} (P := P) (α := α)).symm

namespace HpLuM

def equivM : HpLuM P α ≃ M P α := ABI.equivA.symm

set_option trace.compiler.ir.result true in
@[inline]
def corec
    {β : Type v}
    (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (g : β)
    : HpLuM P α :=
  .mkB <| SM.equivXU <| SM.uLift.{u, v, max u v} <| .corec gen g

/- attribute [macro_inline] TypeVec.splitFun -/

-- TODO: Optimize
set_option trace.compiler.ir.result true in
@[specialize n P α]
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

theorem bisim' {a b : HpLuM.{u} P α} : Bisim a b → a = b := by
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

theorem bisim
    {a b : HpLuM.{u} P α}
    (R : HpLuM.{u} P α → HpLuM.{u} P α → Prop)
    (x : R a b)
    (h : ∀ s t, R s t → ∃ x, ∃ (y z : P.B x ⟹ α ::: HpLuM P α),
      (s.dest.fst = x ∧ s.dest.snd ≍ y) ∧
        (t.dest.fst = x ∧ t.dest.snd ≍ z) ∧ ∀ (i : Fin2 (n + 1)) (j : P.B x i),
        TypeVec.RelLast α R (y i j) (z i j))
    : a = b :=
  bisim' ⟨
    R,
    fun s t h' => (MvPFunctor.liftR_iff _ _ _).mpr <| by 
      conv =>
        rhs; intro _; rhs; intro _; rhs; intro _
        rw [Sigma.ext_iff, Sigma.ext_iff]
      refine h s t h',
    x
  ⟩

end bisim

@[inline]
def corec'
    {β : Type u}
    (gen : β → P (α ::: β))
    : β → HpLuM P α :=
  corec (fun v => .mpr TypeVec.uLift_append1_ULift_uLift <$$> uLift_up.{u,u} (gen v))

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

@[specialize n P α]
def mk : P (α ::: HpLuM P α) → HpLuM P α :=
  corec' ((TypeVec.id ::: dest) <$$> ·)

@[simp]
theorem dest_mk {v : HpLuM P α} : mk (dest v) = v := by
  apply bisim (· = (mk ∘ dest) ·) rfl
  rintro _ x rfl
  dsimp [mk]
  rw [dest_corec']
  refine ⟨
    _, _, _,
    ⟨rfl, heq_of_eq rfl⟩,
    ⟨rfl, (heq_of_eq rfl)⟩,
    fun | .fz, h | .fs s, h => rfl
  ⟩

@[simp]
theorem mk_dest {v : P (α ::: HpLuM P α)} : dest (mk v) = v := by
  have : mk ∘ dest = @id (HpLuM P α) := funext fun x => dest_mk
  rw [mk, dest_corec', ←mk, ←comp_map]
  refine Sigma.ext rfl <| heq_of_eq ?_
  dsimp only [map_fst, map_snd]
  funext i h
  rcases i with (_|i)
  · change (mk ∘ dest) _ = id _
    rw [this]
  · rfl

theorem mk_linv : Function.LeftInverse dest (mk (P := P) (α := α)) :=
  fun _ => mk_dest
theorem dest_linv : Function.LeftInverse (mk (P := P) (α := α)) dest :=
  fun _ => dest_mk

theorem mk.bij : Function.Bijective (mk (P := P) (α := α)) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    dest,
    mk_linv,
    dest_linv,
  ⟩

theorem dest.bij : Function.Bijective (dest (P := P) (α := α)) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    mk,
    dest_linv,
    mk_linv,
  ⟩

theorem mk.inj : Function.Injective     (mk (P := P) (α := α))   := mk.bij.injective
theorem mk.sur : Function.Surjective    (mk (P := P) (α := α))   := mk.bij.surjective
theorem dest.inj : Function.Injective   (dest (P := P) (α := α)) := dest.bij.injective
theorem dest.sur : Function.Surjective  (dest (P := P) (α := α)) := dest.bij.surjective

@[specialize n P α β]
def map {α β : TypeVec.{u} n} (m : α ⟹ β) : HpLuM P α → HpLuM P β :=
  corec' ((m ::: id) <$$> ·.dest)

instance : MvFunctor (HpLuM P) where map := map

theorem id_map (x : HpLuM P α) : TypeVec.id <$$> x = x := by
  apply bisim (· = ·.map TypeVec.id) rfl
  intro _ y rfl
  dsimp [map]
  rw [dest_corec']
  refine ⟨
    _, _, _,
    ⟨rfl, heq_of_eq rfl⟩,
    ⟨rfl, (heq_of_eq rfl)⟩,
    fun | .fz, h | .fs s, h => rfl
  ⟩

theorem comp_map
    {α β γ}
    (g : α ⟹ β) (h : β ⟹ γ)
    (x : HpLuM P α)
    : (h ⊚ g) <$$> x = h <$$> g <$$> x := by
  apply bisim (∃ y, · = y.map (h ⊚ g) ∧ · = (y.map g).map h) ⟨x, rfl, rfl⟩
  rintro a b ⟨y, rfl, rfl⟩
  dsimp [map]
  rw [dest_corec', dest_corec', dest_corec']
  refine ⟨
    _, _, _,
    ⟨rfl, heq_of_eq rfl⟩,
    ⟨rfl, heq_of_eq rfl⟩,
    fun
      | .fz, h => ⟨_, rfl, rfl⟩
      | .fs s, h => rfl
  ⟩

instance : LawfulMvFunctor (HpLuM P) where
  id_map := id_map
  comp_map := comp_map

theorem dest_map
    {α β : TypeVec.{u} n} (g : α ⟹ β) (x : HpLuM P α)
    : dest (g <$$> x) = (g ::: (g <$$> ·)) <$$> dest x := by
  simp only [MvFunctor.map, map, dest_corec']
  refine Sigma.ext (by rfl) <| heq_of_eq ?_
  funext i h
  rcases i with (_|_) <;> rfl

theorem corec_roll
    {α : TypeVec.{u} n}
    {X : Type v}
    {Y : Type w} {x₀ : X}
    (f : X → Y)
    (g : Y → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} X))
    : corec (g ∘ f) x₀ = corec (transliterateMap (ULift.up ∘ f ∘ ULift.down) ∘ g) (f x₀) := by
  apply bisim
    (∃ x, corec (g ∘ f) x = · ∧ corec (transliterateMap (ULift.up ∘ f ∘ ULift.down) ∘ g) (f x) = ·)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨w, rfl, rfl⟩
  rw [dest_corec, dest_corec]
  exact ⟨
    _, _, _,
    ⟨rfl, heq_of_eq rfl⟩,
    ⟨rfl, heq_of_eq rfl⟩,
    fun
      | .fz, h => ⟨_, rfl, rfl⟩
      | .fs s, h => rfl
  ⟩

@[ext 1000]
theorem ext_dest {α : TypeVec n} {x y : HpLuM P α} (h : x.dest = y.dest) : x = y := by
  rw [← dest_mk (v := x), h, dest_mk]

@[ext 0]
theorem ext_mk {α : TypeVec n}
    {x y : P (α ::: HpLuM P α)}
    (h : mk x = mk y)
    : x = y := by
  rw [← mk_dest (v := x), h, mk_dest]

instance inhabited
    {α : TypeVec _}
    [I : Inhabited P.A]
    [df : ∀ i, Inhabited (α i)]
    : Inhabited (HpLuM P α) where
  default := .corec' (fun x =>
    ⟨x, fun | .fz, _ => x | .fs i, _ => (df i).default⟩) I.default

section equivP

variable
    {n : Nat}
    {F : CurriedTypeFun.{u, v} (n + 1)}
    {α : TypeVec.{u} n}
    {P : MvPFunctor (n + 1)}
    [EquivP _ F P]

def mkE : F.app (α ::: HpLuM P α) → HpLuM P α :=
  HpLuM.mk ∘ EquivP.equiv.symm

-- TODO: Get this right
instance : CoeHead (F.app (α ::: HpLuM P α)) (HpLuM P α) where
  coe := mkE

def destE : HpLuM P α → F.app (α ::: HpLuM P α) :=
  EquivP.equiv ∘ HpLuM.dest

@[simp]
theorem destE_mkE
    {v : HpLuM P α}
    : mkE (destE (F := F) v) = v := by
  dsimp [destE, mkE]
  rw [Equiv.symm_apply_apply, HpLuM.dest_mk]

@[simp]
theorem mkE_destE
    {v : F.app (α ::: HpLuM P α)}
    : destE (mkE v) = v := by
  dsimp [destE, mkE]
  rw [HpLuM.mk_dest, Equiv.apply_symm_apply]


@[ext 1000]
theorem ext_destE {α : TypeVec n} {x y : HpLuM P α} (h : x.destE = y.destE) : x = y := by
  rw [← destE_mkE (v := x), h, destE_mkE]

@[ext 0]
theorem ext_mkE {α : TypeVec n} {x y : F.app (α ::: HpLuM P α)} (h : mkE x = mkE y) : x = y := by
  rw [← mkE_destE (v := x), h, mkE_destE]

end equivP

theorem map_corec {γ : Type v} {β : TypeVec n} {f : α ⟹ β}
    {gen : γ → uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} γ)} {g : γ}
    : f <$$> corec gen g = corec ((TypeVec.Arrow.arrow_uLift f ::: id) <$$> gen ·) g := by
  apply bisim
    (fun a b =>
      ∃ y, f <$$> corec gen y = a 
    ∧ corec ((TypeVec.Arrow.arrow_uLift f ::: id) <$$> gen ·) y = b)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨w, rfl, rfl⟩
  simp only [dest_map, dest_corec, map_fst, uLift_down]
  use (gen w).fst.down,
    cast (by simp [dest_map, uLift_down]) ((f <$$> corec gen w).dest.snd)
  simp only [heq_cast_iff_heq, heq_eq_eq, and_self, true_and]
  rw [dest_corec]
  simp only [heq_eq_eq, exists_eq_left']
  rintro (_|i) h
  · change ∃ _, _
    rw! [dest_map, dest_corec]
    exact ⟨_, rfl, rfl⟩
  · change _ = _
    rw! [dest_map, dest_corec]
    rfl

theorem map_corec' {γ : Type u} {β : TypeVec n} {f : α ⟹ β}
    {gen : γ → P (α ::: γ)} {g : γ}
    : f <$$> corec' gen g = corec' ((f ::: id) <$$> gen ·) g := by
  dsimp [corec']
  rw [map_corec]
  congr
  funext x
  rw [MvFunctor.map_map, ←uLift_up_nat, MvFunctor.map_map]
  congr 1
  funext i h
  rcases i with (_|_)
  · rfl
  · rfl

def uLift_up : HpLuM P α → HpLuM (MvPFunctor.uLift.{u, v} P) α.uLift :=
  .corec' (.mpr TypeVec.uLift_append1_ULift_uLift <$$> MvPFunctor.uLift_up ·.down.dest)
    ∘ .up

def uLift_down : HpLuM (MvPFunctor.uLift.{u, v} P) α.uLift → HpLuM P α :=
  .corec (transliterateMap ULift.up ·.dest)

-- It seems I've developed the simp theory enough that these just prove lol
@[simp]
theorem uLift_up_down {x : HpLuM P.uLift α.uLift} : uLift_up (uLift_down x) = x := by
  apply HpLuM.bisim (fun x y => x = y.uLift_down.uLift_up) rfl
  rintro _ x rfl
  simp only [uLift_up, uLift_down, Function.comp_apply, dest_corec', dest_corec, map_fst,
    uLift_up_fst, uLift_down_fst, transliterateMap_fst, ULift.transliterate_down, exists_and_left]
  use x.dest.fst.transliterate
  simp only [ULift.transliterate_def_rev, true_and, heq_eq_eq, ↓existsAndEq, and_true, ]
  rw [dest_corec', dest_corec]
  simp only [ULift.transliterate_noop, map_fst, uLift_up_fst, uLift_down_fst, transliterateMap_fst,
    ULift.transliterate_down, ULift.transliterate_def_rev, map_snd, uLift_up_snd, uLift_down_snd,
    heq_eq_eq, true_and, exists_eq_left', TypeVec.comp.get, Function.comp_apply]
  rintro (_|i) _ <;> rfl

@[simp]
theorem uLift_down_up {x : HpLuM P α} : uLift_down (uLift_up x) = x := by
  apply HpLuM.bisim (fun x y => x = y.uLift_up.uLift_down) rfl
  rintro _ x rfl
  simp only [uLift_down, uLift_up, Function.comp_apply, dest_corec, dest_corec', uLift_down_fst,
    map_fst, transliterateMap_fst, uLift_up_fst, ULift.transliterate_up, exists_and_left]
  use x.dest.fst
  simp only [true_and, heq_eq_eq, exists_eq_left']
  rw [dest_corec, dest_corec', ]
  simp only [uLift_down_fst, map_fst, transliterateMap_fst, uLift_up_fst, ULift.transliterate_up,
    uLift_down_snd, map_snd, heq_eq_eq, exists_eq_left']
  rintro (_|i) _ <;> rfl

namespace transpNatIso

def tf
    {P' : MvPFunctor.{u} (n + 1)}
    (h : NatIso P P')
    {α : TypeVec n}
    : HpLuM P α → P' (α ::: HpLuM P α) :=
  (h ·.dest)
def ti
    {P' : MvPFunctor.{u} (n + 1)}
    (h : NatIso P P')
    {α : TypeVec n}
    : HpLuM P' α → P (α ::: HpLuM P' α) :=
  (h.symm ·.dest)

def transpEquiv
    {P' : MvPFunctor.{u} (n + 1)}
    (h : NatIso P P')
    {α : TypeVec n}
    : HpLuM P α ≃ HpLuM P' α where
  toFun := .corec' (tf h)
  invFun := .corec' (ti h)
  left_inv x := by
    apply bisim (fun x y => x = corec' (ti h) (corec' (tf h) y)) rfl
    rintro s t rfl
    simp only [dest_corec', ti, NatIso.symm, tf, h.nat, Equiv.symm_apply_apply, map_fst]
    use t.dest.fst
    simp only [true_and, heq_eq_eq, exists_and_left, ↓existsAndEq]
    rw [dest_corec', ti, dest_corec', tf]
    dsimp only
    rw [h.symm_nat, h.nat, h.nat]
    rw [MvFunctor.map_map, TypeVec.appendFun_comp', TypeVec.comp_id]
    simp only [NatIso.symm]
    rw [Equiv.symm_apply_apply]
    use ((TypeVec.id ::: corec' (ti h) ∘ corec' (tf h)) <$$> t.dest).snd
    simp only [map_fst, map_snd, heq_eq_eq, TypeVec.comp.get, Function.comp_apply, true_and]
    rintro (_|i) h
    <;> rfl
  right_inv x := by
    apply bisim (fun x y => x = corec' (tf h) (corec' (ti h) y)) rfl
    rintro s t rfl
    simp only [dest_corec', ti, NatIso.symm, tf, h.nat]
    use t.dest.fst
    simp only [heq_eq_eq, true_and, exists_and_left, ↓existsAndEq]
    rw [dest_corec', tf, dest_corec', ti]
    dsimp only
    conv =>
      rhs; intro x; lhs; lhs; lhs
      arg 1; rhs; rhs; rhs
      change h.symm t.dest
    rw [h.symm_nat, h.nat, h.symm_nat]
    rw [MvFunctor.map_map, TypeVec.appendFun_comp', TypeVec.comp_id]
    dsimp only
    simp only [NatIso.symm]
    rw [Equiv.apply_symm_apply]
    use ((TypeVec.id ::: corec' (tf h) ∘ corec' (ti h)) <$$> t.dest).snd
    simp only [map_fst, map_snd, heq_eq_eq, and_self, TypeVec.comp.get, Function.comp_apply,
      true_and]
    rintro (_|i) h
    <;> rfl

end transpNatIso

open transpNatIso in
def transpNatIso
    {P' : MvPFunctor.{u} (n + 1)}
    (h : NatIso P P')
    : NatIso (HpLuM P) (HpLuM P') where
  equiv := transpEquiv h
  nat' {_ _ f} x := by
    dsimp [transpEquiv]
    rw [map_corec']
    change corec' ((f ::: id) <$$> h.equiv ·.dest) x = corec' (h.equiv ·.dest) (f <$$> x)
    apply bisim (fun a b =>
      ∃ y : HpLuM _ _, corec' ((f ::: id) <$$> h.equiv ·.dest) y = a 
      ∧ corec' (h.equiv ·.dest) (f <$$> y) = b
    ) ⟨_, rfl, rfl⟩
    rintro _ _ ⟨w, rfl, rfl⟩
    use (h.equiv w.dest).fst
    simp only [dest_corec', map_fst, true_and]
    rw [dest_corec', MvFunctor.map_map, h.nat]
    rw [TypeVec.appendFun_comp']
    simp only [TypeVec.id_comp, Function.comp_id, exists_and_left]
    use cast (by simp [←h.nat']) 
      (h.equiv ((f ::: corec' fun x ↦ (f ::: id) <$$> h.equiv x.dest) <$$> w.dest)).snd
    simp only [heq_cast_iff_heq, heq_eq_eq, true_and]
    rw [dest_map, ←h.nat']
    simp only [map_fst, true_and]
    use cast (by simp [dest_map, ←h.nat']) (corec' (fun x ↦ h.equiv x.dest) (f <$$> w)).dest.snd
    simp only [heq_cast_iff_heq, heq_eq_eq, true_and]
    rintro (_|i) h'
    · change ∃ _, _
      rw! [←h.nat', dest_corec', dest_map]
      simp only [map_fst, map_snd, cast_eq, TypeVec.comp.get, TypeVec.append1_get_fz,
        TypeVec.appendFun.get_fz, Function.comp_apply]
      rw! [←h.nat']
      exact ⟨_, rfl, rfl⟩
    · change _ = _
      rw! [←h.nat', dest_corec', dest_map]
      simp only [TypeVec.append1_get_fs, map_fst, map_snd, cast_eq, TypeVec.comp.get,
        TypeVec.appendFun.get_fs, Function.comp_apply]
      rw! [←h.nat']
      simp

end Sme.HpLuM


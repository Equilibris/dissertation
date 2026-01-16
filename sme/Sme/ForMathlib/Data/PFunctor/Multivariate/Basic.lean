import Mathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Sme.PFunctor.NatIso

universe u v

namespace MvPFunctor

open MvFunctor (LiftP LiftR)
open scoped MvFunctor

variable {n m : ℕ} {P : MvPFunctor.{u} n} {α : TypeVec n} {β : TypeVec n} {arr : α ⟹ β} {z : P α}

@[simp]
theorem map_fst : (arr <$$> z).fst = z.fst := rfl

@[simp]
theorem map_snd : (arr <$$> z).snd = arr ⊚ z.snd := rfl

@[simp]
theorem map_mk {a b} : (arr <$$> Sigma.mk a b : P β) = (Sigma.mk a (arr ⊚ b) : P β) := rfl

@[pp_with_univ]
def uLift (P : MvPFunctor.{u} n) : MvPFunctor.{max u v} n where
  A := ULift P.A
  B := fun v => (P.B v.down).uLift

variable {P : MvPFunctor.{u} n}

def uLift_down {α : TypeVec.{u} n} (h : uLift.{u, v} P (TypeVec.uLift.{u, v} α)) : P α :=
  ⟨h.fst.down, h.snd.uLift_arrow⟩

def uLift_up {α : TypeVec.{u} n} (h : P α) : uLift.{u, v} P (TypeVec.uLift.{u, v} α) :=
  ⟨.up h.fst, h.snd.arrow_uLift⟩

@[simp]
theorem uLift_up_fst (h : P α) : (uLift_up h).fst = .up h.fst := rfl

@[simp]
theorem uLift_up_snd (h : P α) : (uLift_up h).snd = h.snd.arrow_uLift := rfl

@[simp]
theorem uLift_down_fst (h : uLift.{u, v} P (TypeVec.uLift.{u, v} α))
    : (uLift_down h).fst = h.fst.down := rfl

@[simp]
theorem uLift_down_snd (h : uLift.{u, v} P (TypeVec.uLift.{u, v} α))
    : (uLift_down h).snd = h.snd.uLift_arrow := rfl

theorem uLift_down_nat (h : uLift.{u, v} P (TypeVec.uLift.{u, v} α))
    {β} {f : α ⟹ β}
    : f <$$> uLift_down h = uLift_down (.arrow_uLift f <$$> h) := rfl

theorem uLift_up_nat (h : P α)
    {β} {f : α ⟹ β}
    : .arrow_uLift f <$$> uLift_up h = uLift_up (f <$$> h) := rfl

namespace comp

variable
    {P : MvPFunctor.{u} n}
    {Q : Fin2 n → MvPFunctor.{u} m}
    {α β : TypeVec.{u} m}
    {mv : P (Q · α)}

theorem map_mk {f : α ⟹ β}
    : f <$$> comp.mk mv = comp.mk ((fun _ v => f <$$> v) <$$> mv) :=
  rfl

def equi : P (Q · α) ≃ P.comp Q α where
  toFun := comp.mk
  invFun := comp.get

theorem mk_bij
    : Function.Bijective (comp.mk : P (Q · α) → P.comp Q α) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    comp.get,
    comp.get_mk,
    comp.mk_get,
  ⟩
theorem get_bij
    : Function.Bijective (comp.get : (P.comp Q) α → (P (Q · α))) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    comp.mk,
    comp.mk_get,
    comp.get_mk,
  ⟩

def uLift
    : NatIso (P.comp Q).uLift (P.uLift.comp (MvPFunctor.uLift ∘ Q)) where
  equiv := {
    toFun v := ⟨
        ⟨.up v.1.down.1, fun i h => .up <| v.fst.down.snd i h.down⟩,
        v.2 ⊚ fun _ h => ULift.up ⟨h.1, h.2.1.down, h.2.2.down⟩
      ⟩
    invFun v := ⟨
        ⟨v.1.1.down, fun i h => (v.1.2 i (.up h)).down⟩,
        v.2 ⊚ fun _ h => ⟨h.down.1, .up h.down.2.1, .up h.down.2.2⟩
      ⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  nat' _ := rfl

def equivTfn
    {P' : MvPFunctor.{u} n}
    (hP : ∀ α, P α ≃ P' α)
    : P.comp Q α ≃ P'.comp Q α := calc
  _ ≃ P (Q · α)     := equi.symm
  _ ≃ P' (Q · α)    := hP _
  _ ≃ P'.comp Q α   := equi

def equivTarg
    {Q' : Fin2 n → MvPFunctor.{u} m}
    (hQ : ∀ i α, Q i α ≃ Q' i α)
    : P.comp Q α ≃ P.comp Q' α := calc
  _ ≃ P (Q · α)     := equi.symm
  _ ≃ P (Q' · α)    := {
      toFun v :=  (hQ · α) <$$> v
      invFun v := (hQ · α |>.symm) <$$> v
      left_inv v := by
        dsimp only
        rw [MvFunctor.map_map]
        change (fun i x ↦ (hQ i α).symm ((hQ i α) x)) <$$> v = v
        simp
      right_inv v := by
        dsimp only
        rw [MvFunctor.map_map]
        change (fun i x ↦ (hQ i α) ((hQ i α).symm x)) <$$> v = v
        simp
    }
  _ ≃ P.comp Q' α   := equi

def niLift
    {P' : MvPFunctor.{u} n}
    {Q' : Fin2 n → MvPFunctor.{u} m}
    (hP : NatIso P P')
    (hQ : ∀ i, NatIso (Q i) (Q' i))
    : NatIso (P.comp Q) (P'.comp Q') where
  equiv := calc
    _ ≃ _ := equivTfn (fun α => hP.equiv)
    _ ≃ _ := equivTarg fun i α => (hQ i).equiv
  nat' x := by
    simp only [equivTfn, equi, Equiv.trans_def, equivTarg, Equiv.trans_apply, Equiv.coe_fn_symm_mk,
      Equiv.coe_fn_mk, get_mk, hP.nat, map_mk, MvFunctor.map_map, get_map]
    congr 3
    funext i h
    simp [(hQ i).nat]

theorem get_fst (x : P.comp Q α) : (comp.get x).fst = x.fst.fst := rfl
theorem mk_fst (x : P (Q · α)) : (comp.mk x).fst = ⟨x.fst, (x.snd · · |>.fst)⟩ := rfl
theorem get_snd (x : P.comp Q α)
    : (comp.get x).snd = (fun i a ↦ ⟨x.fst.snd i a, fun j b ↦ x.snd j ⟨i, ⟨a, b⟩⟩⟩) :=
  rfl
theorem mk_snd (x : P (Q · α)) 
    : (comp.mk x).snd = (fun i a ↦ (x.snd a.fst a.snd.fst).snd i a.snd.snd) :=
  rfl

@[simp]
theorem B_eq {α i} : (comp P Q).B α i = ((j : Fin2 n) × (b : P.B α.fst j) × (Q j).B (α.snd j b) i) :=
  rfl

end comp

end MvPFunctor


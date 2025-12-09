import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.CongrExclamation

universe u v w x y z

variable {A : Type u} {B : Type v}

namespace NonOmegaABI

@[pp_with_univ]
structure ABIRepr.{low, hi, e} (A : Type low) (B : Type hi) (eq : A ≃ B)
    : Type max hi (e + 1) (low + 1) where
  intro ::
  carry : Type low

  mkB : B → carry
  mkA : A → carry

  destB : carry → B
  destA : carry → A

  mkB_destB : destB ∘ mkB = id
  destB_mkB : mkB ∘ destB = id

  mkA_destA : destA ∘ mkA = id
  destA_mkA : mkA ∘ destA = id

  toFun_mkB_mkA  : mkB ∘ eq.toFun = mkA
  invFun_mkA_mkB : mkA ∘ eq.invFun = mkB

  destA_toFun_destB  : eq ∘ destA = destB
  destB_invFun_destA : eq.symm ∘ destB = destA

  elim : {motive : carry → Type e}
       → (hLog : (z : A) → motive (mkA z))
       → (hCheap : (z : B) → motive (mkB z))
       → (eqA : ∀ z, hLog z ≍ hCheap (eq z))
       → (eqB : ∀ z, hCheap z ≍ hLog (eq.symm z))
       → (v : carry) → motive v

  elimLog : {motive : carry → Type e}
       → {hLog : (z : A) → motive (mkA z)}
       → {hCheap : (z : B) → motive (mkB z)}
       → {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
       → {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
       → ∀ z, elim hLog hCheap eqA eqB (mkA z) = (hLog z)
  elimCheap : {motive : carry → Type e}
       → {hLog : (z : A) → motive (mkA z)}
       → {hCheap : (z : B) → motive (mkB z)}
       → {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
       → {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
       → ∀ z : B, elim hLog hCheap eqA eqB (mkB z) = (hCheap z)

@[simp]
unsafe def unsafeCastNoop {v : Type _} : unsafeCast (α := v) (β := v) = id := rfl

section corruptionSurface

@[simp]
unsafe axiom unsafeCastComp {α β χ : Type _}
    : unsafeCast (α := β) (β := χ) ∘ unsafeCast = unsafeCast (α := α) (β := χ)
unsafe abbrev unsafeIn : B → unsafeCast B := unsafeCast
unsafe abbrev unsafeOut : unsafeCast B → B := unsafeCast

end corruptionSurface

private unsafe def ABIImpl (A : Type u) (B : Type v) (eq : A ≃ B)
    : ABIRepr.{u, v, w} A B eq := {
  carry := unsafeCast B,
  mkA := unsafeIn ∘ eq,
  mkB := unsafeIn,
  destA := eq.symm ∘ unsafeOut,
  destB := unsafeOut,
  mkB_destB := unsafeCastComp
  destB_mkB := unsafeCastComp
  mkA_destA := calc
    eq.symm ∘ (unsafeCast ∘ unsafeCast) ∘ eq
      = eq.symm ∘ id ∘ eq             := by rw [unsafeCastComp, unsafeCastNoop]
    _ = id                            := Equiv.symm_comp_self eq 
  destA_mkA := calc
    unsafeCast ∘ (eq ∘ eq.symm) ∘ unsafeCast
      = unsafeCast ∘ id ∘ unsafeCast  := by rw [Equiv.self_comp_symm eq]
    _ = id                            := unsafeCastComp.trans unsafeCastNoop
  toFun_mkB_mkA := rfl
  invFun_mkA_mkB := calc
    unsafeCast ∘ (eq ∘ eq.symm)
      = unsafeIn ∘ id                 := by rw [Equiv.self_comp_symm]
    _ = unsafeIn                      := rfl
  destA_toFun_destB := calc
    (eq ∘ eq.symm) ∘ unsafeOut
      = id ∘ unsafeOut                := by rw [Equiv.self_comp_symm]
    _ = unsafeOut                     := rfl
  destB_invFun_destA := rfl
  elim := fun {motive} _ hCheap _ _ x =>
    cast (by rw [unsafeCastComp]; rfl) <|
      show motive ((unsafeCast ∘ unsafeCast) x)
      from hCheap <| unsafeOut x
  elimLog := fun {_ hLog hCheap eqA _ z} => by
    apply eq_of_heq
    change cast _ (hCheap ((unsafeCast ∘ unsafeCast) _)) ≍ hLog z
    apply HEq.trans (cast_heq _ _)
    rw [unsafeCastComp, unsafeCastNoop]
    exact (eqA z).symm
  elimCheap := fun {_ hLog hCheap _ _ x} => by
    apply eq_of_heq
    change cast _ (hCheap ((unsafeCast ∘ unsafeCast) _)) ≍ hCheap (id x)
    apply HEq.trans (cast_heq _ _)
    rw [unsafeCastComp, unsafeCastNoop]
}

@[implemented_by ABIImpl]
opaque ABI (A : Type u) (B : Type v) (eq : A ≃ B)
    : ABIRepr.{u, v, w} A B eq := {
  carry := A,
  mkA := id,
  mkB := eq.invFun,
  destA := id,
  destB := eq.toFun,
  mkB_destB := Equiv.self_comp_symm eq
  destB_mkB := Equiv.symm_comp_self eq
  mkA_destA := rfl
  destA_mkA := rfl
  toFun_mkB_mkA := Equiv.symm_comp_self eq
  invFun_mkA_mkB := rfl
  destA_toFun_destB := rfl
  destB_invFun_destA := Equiv.symm_comp_self eq
  elim := fun {_ hLog _ _ _ x} => hLog x
  elimLog := fun {_ hLog _ _ _ x} => Eq.refl (hLog x)
  elimCheap := fun {_ _ _ _ eqB x} => eq_of_heq ((eqB x).symm)
}

namespace ABIRepr

attribute [elab_as_elim] ABIRepr.elim

variable {eq : A ≃ B} {r : ABIRepr.{u, v, w} A B eq}

def equivA : A ≃ r.carry where
  toFun  := r.mkA
  invFun := r.destA
  left_inv  := fun a => by
    change (_ ∘ _) a = id _
    rw [mkA_destA]
  right_inv := fun a => by
    change (_ ∘ _) a = id _
    rw [destA_mkA]

def equivB : B ≃ r.carry where
  toFun  := r.mkB
  invFun := r.destB
  left_inv  := fun a => by
    change (_ ∘ _) a = id _
    rw [mkB_destB]
  right_inv := fun a => by
    change (_ ∘ _) a = id _
    rw [destB_mkB]

namespace carry

def mkB : B → r.carry := r.mkB
def mkA : A → r.carry := r.mkA
def destB : r.carry → B := r.destB
def destA : r.carry → A := r.destA

section eqs

@[simp] theorem mkB_destB : destB (r := r) ∘ mkB = id := r.mkB_destB
@[simp] theorem destB_mkB : mkB (r := r) ∘ destB = id := r.destB_mkB
@[simp] theorem mkA_destA : destA (r := r) ∘ mkA = id := r.mkA_destA
@[simp] theorem destA_mkA : mkA (r := r) ∘ destA = id := r.destA_mkA

@[simp] theorem toFun_mkB_mkA : mkB (r := r) ∘ eq = mkA := r.toFun_mkB_mkA
@[simp] theorem invFun_mkA_mkB : mkA (r := r) ∘ eq.symm = mkB := r.invFun_mkA_mkB
@[simp] theorem destA_toFun_destB : eq ∘ destA (r := r) = destB := r.destA_toFun_destB
@[simp] theorem destB_invFun_destA : eq.symm ∘ destB (r := r) = destA := r.destB_invFun_destA

@[simp] theorem destB_mkA_toFun : destB (r := r) ∘ mkA = eq := by
  rw [←toFun_mkB_mkA, ←Function.comp_assoc, mkB_destB, Function.id_comp]

@[simp] theorem destA_mkB_toInv : destA (r := r) ∘ mkB = eq.symm := by
  rw [←invFun_mkA_mkB, ←Function.comp_assoc, mkA_destA, Function.id_comp]

@[simp] theorem mkB_destB' {v} : destB (r := r) (mkB v) = v := by
  change (destB ∘ mkB) v = id v
  rw [mkB_destB]
@[simp] theorem destB_mkB' {v} : mkB (r := r) (destB v) = v := by
  change (mkB ∘ destB) v = id v
  rw [destB_mkB]

@[simp] theorem mkA_destA' {v} : destA (r := r) (mkA v) = v := by
  change (destA ∘ mkA) v = id v
  rw [mkA_destA]
@[simp] theorem destA_mkA' {v} : mkA (r := r) (destA v) = v := by
  change (mkA ∘ destA) v = id v
  rw [destA_mkA]

@[simp] theorem toFun_mkB_mkA' {v} : mkB (r := r) (eq v) = mkA v := by
  change (mkB ∘ eq) v = mkA v
  rw [toFun_mkB_mkA]
@[simp] theorem invFun_mkA_mkB' {v} : mkA (r := r) (eq.symm v) = mkB v := by
  change (mkA ∘ eq.symm) v = mkB v
  rw [invFun_mkA_mkB]

@[simp] theorem destA_toFun_destB' {v} : eq (destA (r := r) v) = destB v := by
  change (eq ∘ destA) v = destB v
  rw [destA_toFun_destB]
@[simp] theorem destB_invFun_destA' {v} : eq.symm (destB (r := r) v) = destA v := by
  change (eq.symm ∘ destB) v = destA v
  rw [destB_invFun_destA]

@[simp] theorem destB_mkA_toFun' {v} : destB (r := r) (mkA v) = eq v := by
  change (destB ∘ mkA) v = eq v
  rw [destB_mkA_toFun]
@[simp] theorem destA_mkB_toInv' {v} : destA (r := r) (mkB v) = eq.symm v := by
  change (destA ∘ mkB) v = eq.symm v
  rw [destA_mkB_toInv]

end eqs

variable {r : ABIRepr.{_, _, max w x} A B eq}

def elim {motive : r.carry → Sort x}
     (hLog : (z : A) → motive (mkA z))
     (hCheap : (z : B) → motive (mkB z))
     (eqA : ∀ z, hLog z ≍ hCheap (eq z))
     (eqB : ∀ z, hCheap z ≍ hLog (eq.symm z))
     (v : r.carry) : motive v :=
  PLift.down
  <| PULift.down
  <| r.elim
      (.up <| .up <| hLog ·)
      (.up <| .up <| hCheap ·)
      (by
        rw! (castMode := .all) [eqA ·]
        congr! 3
        any_goals (rw [←r.toFun_mkB_mkA]; rfl)
        exact cast_heq _ _
      )
      (by
        rw! (castMode := .all) [eqB ·]
        congr! 3
        any_goals (rw [←r.invFun_mkA_mkB]; rfl)
        exact cast_heq _ _
      )
      v

theorem elimLog {motive : r.carry → Sort x}
     {hLog : (z : A) → motive (mkA z)}
     {hCheap : (z : B) → motive (mkB z)}
     {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
     {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
     z : elim hLog hCheap eqA eqB (mkA z) = hLog z := by
  dsimp [elim, mkA]
  rw! [ABIRepr.elimLog r z]

theorem elimCheap {motive : r.carry → Sort x}
     {hLog : (z : A) → motive (mkA z)}
     {hCheap : (z : B) → motive (mkB z)}
     {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
     {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
    z : elim hLog hCheap eqA eqB (mkB z) = hCheap z := by
  dsimp [elim, mkB]
  rw! [ABIRepr.elimCheap r z]

-- Hide the impl
attribute [irreducible] elim

instance : CoeSort (ABIRepr A B eq) (Type _) := ⟨ABIRepr.carry⟩

-- TODO: Make a version where a and b dont both reside in w
@[ext]
theorem extB
    {a : ABI.{u, v, w} _ _ eq} {b : ABI.{u, v, w} _ _ eq}
    (h : a.destB = b.destB)
    : a = b := by
  induction a using ABIRepr.carry.elim <;> induction b using ABIRepr.carry.elim
  any_goals simp only [carry.mkB_destB', carry.destB_mkA_toFun', EmbeddingLike.apply_eq_iff_eq] at h
  any_goals subst h
  any_goals simp

theorem extA
    {a : ABI.{u, v, w} _ _ eq} {b : ABI.{u, v, w} _ _ eq}
    (h : a.destA = b.destA)
    : a = b := by
  induction a using ABIRepr.carry.elim <;> induction b using ABIRepr.carry.elim
  any_goals simp only [carry.mkA_destA', EmbeddingLike.apply_eq_iff_eq, carry.destA_mkB_toInv'] at h
  any_goals subst h
  any_goals simp

section transliterate

-- A form of casting, but without equalties
@[pp_with_univ]
def transliterateB.{a, b, u', v'}
    {A B}
    {eq : A ≃ B}
    (a : ABI.{u', v', a} _ _ eq)
    : ABI.{u', v', b} _ _ eq := .mkB a.destB

@[simp] theorem transliterateB_mkA : transliterateB ∘ .mkA (eq := eq) = .mkA := by
  change _ ∘ carry.destB ∘ _ = _; simp
@[simp] theorem transliterateB_mkA' {v} : transliterateB (.mkA (eq := eq) v) = .mkA v := by
  simp [transliterateB]

@[simp] theorem transliterateB_mkB : transliterateB ∘ .mkB (eq := eq) = .mkB := by
  change _ ∘ carry.destB ∘ _ = _; simp
@[simp] theorem transliterateB_mkB' {v} : transliterateB (.mkB (eq := eq) v) = .mkB v := by
  simp [transliterateB]

@[simp] theorem destA_transliterateB' {v}
    : carry.destA (transliterateB (eq := eq) v) = carry.destA v := by
  simp [transliterateB]
@[simp] theorem destA_transliterateB : carry.destA (eq := eq) ∘ transliterateB = carry.destA := by
  funext v
  simp

@[simp] theorem destB_transliterateB' {v}
    : carry.destB (transliterateB (eq := eq) v) = carry.destB v := by
  simp [transliterateB]
@[simp] theorem destB_transliterateB : carry.destB (eq := eq) ∘ transliterateB = carry.destB := by
  funext v
  simp

@[simp] theorem transliterateB_idempotent' {v}
    : transliterateB (eq := eq) (transliterateB v) = transliterateB v := by
  simp [transliterateB]
@[simp] theorem transliterateB_idempotent
    : transliterateB (eq := eq) ∘ transliterateB = transliterateB := by
  funext v; simp

@[simp] theorem transliterateB_id
    : transliterateB (eq := eq) = id := by
  change _ ∘ _ = _; simp
@[simp] theorem transliterateB_id' {v}
    : transliterateB (eq := eq) v = v := by
  simp [transliterateB]

@[simp] theorem transliterateB_inv.{a, b}
    : transliterateB.{b, a} (eq := eq) ∘ transliterateB.{a, b} = id := by
  simp
@[simp] theorem transliterateB_inv'.{a, b} {v}
    : transliterateB.{b, a} (eq := eq) (transliterateB.{a, b} v) = v := by
  simp

end transliterate

section freeelim

@[elab_as_elim]
def rec {motive : ABI.{u, v, w} A B eq → Sort x}
     (hLog : (z : A) → motive (mkA z))
     (hCheap : (z : B) → motive (mkB z))
     (eqA : ∀ z, hLog z ≍ hCheap (eq z))
     (eqB : ∀ z, hCheap z ≍ hLog (eq.symm z))
     (v : _) : motive v :=
  cast (congr rfl <| transliterateB_inv'.{_,_,_,max x x} (v := v)) <| by
  induction (transliterateB.{w, x, u, v} v) using carry.elim
  case hLog z =>
    exact cast (congr rfl transliterateB_mkA'.symm) <| hLog z
  case hCheap z =>
    exact cast (congr rfl transliterateB_mkB'.symm) <| hCheap z
  · simp [eqA]
  · simp [eqB]

theorem recLog {motive : ABI.{u, v, w} A B eq → Sort x}
     {hLog : (z : A) → motive (mkA z)}
     {hCheap : (z : B) → motive (mkB z)}
     {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
     {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
     z : rec hLog hCheap eqA eqB (mkA z) = hLog z := by
  dsimp [rec, mkA]
  apply eq_of_heq
  apply HEq.trans
  · exact cast_heq _ _
  change elim _ _ _ _ (transliterateB (carry.mkA _)) ≍ _
  rw [transliterateB_mkA', carry.elimLog]
  exact cast_heq _ _
theorem recCheap {motive : ABI.{u, v, w} A B eq → Sort x}
     {hLog : (z : A) → motive (mkA z)}
     {hCheap : (z : B) → motive (mkB z)}
     {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
     {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
     z : rec hLog hCheap eqA eqB (mkB z) = hCheap z := by
  dsimp [rec, mkA]
  apply eq_of_heq
  apply HEq.trans
  · exact cast_heq _ _
  change elim _ _ _ _ (transliterateB (carry.mkB _)) ≍ _
  rw [transliterateB_mkB', carry.elimCheap]
  exact cast_heq _ _

attribute [irreducible] rec

end freeelim

end NonOmegaABI.ABIRepr.carry

@[pp_with_univ]
def ABI A B eq := (NonOmegaABI.ABI.{u, v, 0} A B eq).carry

namespace ABI

open NonOmegaABI.ABIRepr
open NonOmegaABI.ABIRepr.carry

variable {eq : A ≃ B}

def mkA : A → ABI A B eq := carry.mkA
def mkB : B → ABI A B eq := carry.mkB
def destA : ABI A B eq → A := carry.destA
def destB : ABI A B eq → B := carry.destB

section eqs

@[simp] theorem mkB_destB : destB (eq := eq) ∘ mkB = id := carry.mkB_destB
@[simp] theorem destB_mkB : mkB (eq := eq) ∘ destB = id := carry.destB_mkB
@[simp] theorem mkA_destA : destA (eq := eq) ∘ mkA = id := carry.mkA_destA
@[simp] theorem destA_mkA : mkA (eq := eq) ∘ destA = id := carry.destA_mkA

@[simp] theorem toFun_mkB_mkA : mkB (eq := eq) ∘ eq = mkA := carry.toFun_mkB_mkA
@[simp] theorem invFun_mkA_mkB : mkA (eq := eq) ∘ eq.symm = mkB := carry.invFun_mkA_mkB
@[simp] theorem destA_toFun_destB : eq ∘ destA (eq := eq) = destB := carry.destA_toFun_destB
@[simp] theorem destB_invFun_destA : eq.symm ∘ destB (eq := eq) = destA := carry.destB_invFun_destA

@[simp] theorem destB_mkA_toFun : destB (eq := eq) ∘ mkA = eq := carry.destB_mkA_toFun
@[simp] theorem destA_mkB_toInv : destA (eq := eq) ∘ mkB = eq.symm := carry.destA_mkB_toInv

variable {v}

@[simp] theorem mkB_destB' : destB (eq := eq) (mkB v) = v := carry.mkB_destB'
@[simp] theorem destB_mkB' : mkB (eq := eq) (destB v) = v := carry.destB_mkB'

@[simp] theorem mkA_destA' : destA (eq := eq) (mkA v) = v := carry.mkA_destA'
@[simp] theorem destA_mkA' : mkA (eq := eq) (destA v) = v := carry.destA_mkA'

@[simp] theorem toFun_mkB_mkA' : mkB (eq := eq) (eq v) = mkA v := carry.toFun_mkB_mkA'
@[simp] theorem invFun_mkA_mkB' : mkA (eq := eq) (eq.symm v) = mkB v := carry.invFun_mkA_mkB'

@[simp] theorem destA_toFun_destB' : eq (destA (eq := eq) v) = destB v := carry.destA_toFun_destB'
@[simp] theorem destB_invFun_destA' : eq.symm (destB (eq := eq) v) = destA v :=
  carry.destB_invFun_destA'

@[simp] theorem destB_mkA_toFun' : destB (eq := eq) (mkA v) = eq v := carry.destB_mkA_toFun'
@[simp] theorem destA_mkB_toInv' : destA (eq := eq) (mkB v) = eq.symm v := carry.destA_mkB_toInv'

theorem mkA_inj : Function.Injective (mkA (eq := eq)) :=
  fun a b h => by
    change id a = id b
    repeat rw [←mkA_destA (eq := eq)]
    dsimp
    rw [h]
theorem mkB_inj : Function.Injective (mkB (eq := eq)) :=
  fun a b h => by
    change id a = id b
    repeat rw [←mkB_destB (eq := eq)]
    dsimp
    rw [h]

theorem mkA_mkB_iff_eq {a : A} {b : B} : mkA (eq := eq) a = mkB b ↔ eq a = b where
  mp h := by
    change id (eq a) = id b
    repeat rw [←mkB_destB (eq := eq)]
    change (mkB (eq a)).destB = (mkB b).destB
    rw [toFun_mkB_mkA', h]
  mpr h := by rw [←toFun_mkB_mkA', h]

theorem mkA_mkB_iff_eq_symm {a : A} {b : B} : mkA (eq := eq) a = mkB b ↔ a = eq.symm b where
  mp h := by
    change id a = id (eq.symm b)
    repeat rw [←mkA_destA (eq := eq)]
    dsimp
    rw [h, destA_mkB_toInv', invFun_mkA_mkB', destA_mkB_toInv']
  mpr h := by rw [h, invFun_mkA_mkB']

def equivA : A ≃ ABI _ _ eq where
  toFun  := ABI.mkA
  invFun := ABI.destA
  left_inv  := fun a => by
    change (carry.destA ∘ carry.mkA) a = id _
    rw [carry.mkA_destA]
  right_inv := fun a => by
    change (carry.mkA ∘ carry.destA) a = id _
    rw [carry.destA_mkA]

def equivB : B ≃ ABI _ _ eq where
  toFun  := ABI.mkB
  invFun := ABI.destB
  left_inv  := fun a => by
    change (carry.destB ∘ carry.mkB) a = id _
    rw [carry.mkB_destB]
  right_inv := fun a => by
    change (carry.mkB ∘ carry.destB) a = id _
    rw [carry.destB_mkB]

end eqs

section

@[elab_as_elim] def rec
    : {motive : ABI.{u, v} A B eq → Sort x}
    → (hLog : (z : A) → motive (mkA z))
    → (hCheap : (z : B) → motive (mkB z))
    → (eqA : ∀ z, (hLog z) ≍ (hCheap (eq z)))
    → (eqB : ∀ z, (hCheap z) ≍ (hLog (eq.symm z)))
    → (v : _) → motive v := carry.rec

@[simp] theorem recLog
    : {motive : ABI.{u, v} A B eq → Sort x}
    → {hLog : (z : A) → motive (mkA z)}
    → {hCheap : (z : B) → motive (mkB z)}
    → {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
    → {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
    → (z : _)
    → rec hLog hCheap eqA eqB (mkA z) = hLog z := carry.recLog
@[simp] theorem recCheap
    : {motive : ABI.{u, v} A B eq → Sort x}
    → {hLog : (z : A) → motive (mkA z)}
    → {hCheap : (z : B) → motive (mkB z)}
    → {eqA : ∀ z, hLog z ≍ hCheap (eq z)}
    → {eqB : ∀ z, hCheap z ≍ hLog (eq.symm z)}
    → (z : _)
    → rec hLog hCheap eqA eqB (mkB z) = hCheap z := carry.recCheap

end

theorem extB' {a b : ABI.{u, v} _ _ eq} : a.destB = b.destB → a = b := carry.extB
theorem extA' {a b : ABI.{u, v} _ _ eq} : a.destA = b.destA → a = b := carry.extA

theorem extB
    {a b : ABI.{u, v} _ _ eq}
    : (∀ x y, a = .mkB x → b = .mkB y → x = y) → a = b :=
  fun h => extB' <| h (destB a) (destB b) destB_mkB'.symm destB_mkB'.symm
theorem extA
    {a b : ABI.{u, v} _ _ eq}
    : (∀ x y, a = .mkA x → b = .mkA y → x = y) → a = b :=
  fun h => extA' <| h (destA a) (destA b) destA_mkA'.symm destA_mkA'.symm

attribute [irreducible] rec mkA mkB destA destB

section

def lift {motive : Sort x}
    (fa : A → motive)
    (fb : B → motive)
    (eqa : fa = fb ∘ eq)
    (eqb : fb = fa ∘ eq.symm)
    : ABI _ _ eq → motive :=
  rec fa fb
    (heq_of_eq <| congrFun eqa ·)
    (heq_of_eq <| congrFun eqb ·)

@[simp] theorem liftA
    {a motive} {fa : A → motive} {fb : B → motive}
    {eqa : fa = fb ∘ eq} {eqb : fb = fa ∘ eq.symm}
    : lift fa fb eqa eqb (mkA a) = fa a := recLog a
@[simp] theorem liftB
    {b motive} {fa : A → motive} {fb : B → motive}
    {eqa : fa = fb ∘ eq} {eqb : fb = fa ∘ eq.symm}
    : lift fa fb eqa eqb (mkB b) = fb b := recCheap b

end

end ABI


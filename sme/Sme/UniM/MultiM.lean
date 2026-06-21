import Sme.AltRepr
import Sme.HEq
import Sme.UniM.HpLuM
import Sme.PFunctor.Utils
import Mathlib.Logic.Small.Defs

open MvPFunctor

namespace Sme

universe u v w x

variable {n : Nat} (P : MvPFunctor.{u} n.succ)

/-- A path from the root of a tree to one of its node -/
inductive M.Path : (Uni.M P.last) → Fin2 n → Type u
  | root (x : _)
          (a : P.A)
          (f : P.last.B a → Uni.M P.last)
          (h : x.dest = ⟨a, f⟩)
          (i : Fin2 n)
          (c : P.drop.B a i) : M.Path x i
  | child (x : _)
          (a : P.A)
          (f : P.last.B a → Uni.M P.last)
          (h : x.dest = ⟨a, f⟩)
          (j : P.last.B a)
          (i : Fin2 n)
          (c : M.Path (f j) i) : M.Path x i

instance M.Path.inhabited (x : Uni.M P.last) {i}
    [Inhabited (P.drop.B x.head i)] : Inhabited (M.Path P x i) :=
  ⟨M.Path.root _ x.head x.children (by cases x using Uni.M.mk_cases; rfl) _ default⟩

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `mp α` is made of a tree and a function
from its valid paths to the values it contains -/
def mp : MvPFunctor n where
  A := Uni.M P.last
  B := M.Path P

/-- `n`-ary M-type for `P` -/
def M (α : TypeVec n) : Type u :=
  mp P α

@[reducible]
instance : MvFunctor (M P) := by
  change MvFunctor (mp P)
  infer_instance

/- instance {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin2 n, Inhabited (α i)]  -/
/-     : Inhabited (P.M α) := -/
/-   @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _ -/

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corecShape {β : Type v} (g₀ : β → P.A) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) :
    β → Uni.M P.last :=
  Uni.M.corec fun b => ⟨g₀ b, g₂ b⟩

open scoped MvFunctor

/-- Proof of type equality as an arrow -/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' := fun _i b => Eq.recOn h b

/-- Proof of type equality as a function -/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' := fun b => Eq.recOn h b

/-- Using corecursion, construct the contents of an M-type -/
def M.corecContents {α : TypeVec.{u} n}
    {β : Type v}
    (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β)
    (x : _)
    (b : β)
    (h : x = M.corecShape P g₀ g₂ b) :
    M.Path P x ⟹ α
  | _, M.Path.root x a f h' i c =>
    have : a = g₀ b := by
      rw [h, M.corecShape, Uni.M.dest_corec] at h'
      cases h'
      rfl
    g₁ b i (P.castDropB this i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      rw [h, M.corecShape, Uni.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : f j = M.corecShape P g₀ g₂ (g₂ b (castLastB P h₀ j)) := by
      rw [h, M.corecShape, Uni.M.dest_corec] at h'
      cases h'
      rfl
    M.corecContents g₀ g₁ g₂ (f j) (g₂ b (P.castLastB h₀ j)) h₁ i c

/-- Corecursor for M-type of `P` -/
def M.corec'
    {α : TypeVec n} {β : Type w} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (b : β)
    : M P α where
  fst := corecShape P g₀ g₂ b
  snd := M.corecContents P g₀ g₁ g₂ _ _ rfl

variable {P}

/-- Corecursor for M-type of `P` -/
def M.corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) : β → M P α :=
  M.corec' P
    (fun b => (g b).fst)
    (fun b => TypeVec.dropFun (g b).snd)
    (fun b => TypeVec.lastFun (g b).snd)

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestLeft {α : TypeVec n} {x : Uni.M P.last} {a : P.A} {f : P.last.B a → Uni.M P.last}
    (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c =>
  f' i (M.Path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestRight {α : TypeVec n} {x : Uni.M P.last} {a : P.A} {f : P.last.B a → Uni.M P.last}
    (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α)
    (j : P.last.B a)
    : M.Path P (f j) ⟹ α := fun i c => f' i (M.Path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
def M.dest' {α : TypeVec n} {x : Uni.M P.last} {a : P.A} {f : P.last.B a → Uni.M P.last}
    (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P (α.append1 (M P α)) :=
  ⟨a, TypeVec.splitFun (M.pathDestLeft h f') fun x => ⟨f x, M.pathDestRight h f' x⟩⟩

/-- Destructor for M-types -/
def M.dest {α : TypeVec n} (x : M P α) : P (α ::: M P α) :=
  M.dest'
    (Sigma.eta <| (x.fst).dest).symm
    x.snd

/-- Constructor for M-types -/
def M.mk {α : TypeVec n} : P (α.append1 (M P α)) → M P α :=
  M.corec fun i => TypeVec.appendFun TypeVec.id dest <$$> i

theorem M.dest'_eq_dest' {α : TypeVec n} {x : Uni.M P.last} {a₁ : P.A}
    {f₁ : P.last.B a₁ → Uni.M P.last} (h₁ : x.dest = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.last.B a₂ → Uni.M P.last} (h₂ : x.dest = ⟨a₂, f₂⟩) (f' : M.Path P x ⟹ α) :
    M.dest' h₁ f' = M.dest' h₂ f' := by cases h₁.symm.trans h₂; rfl

theorem M.dest_eq_dest' {α : TypeVec n} {x : Uni.M P.last} {a : P.A}
    {f : P.last.B a → Uni.M P.last} (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    M.dest ⟨x, f'⟩ = M.dest' h f' :=
  M.dest'_eq_dest' _ _ _

theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type v} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (x : β)
    : M.dest
      (M.corec' P g₀ g₁ g₂ x)
    = ⟨g₀ x, TypeVec.splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=by
  simp only [Nat.succ_eq_add_one, dest, dest', corec', TypeVec.drop_append1_simp, TypeVec.last_eq,
    TypeVec.append1_get_fz]
  simp only [corecShape]
  rw! [Uni.M.dest_corec]
  refine Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => ?_
  <;> rfl

@[simp]
theorem M.dest_corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) (x : β) 
    : M.dest (M.corec g x) = TypeVec.appendFun TypeVec.id (M.corec g) <$$> g x := by
  trans
  · apply M.dest_corec'
  have ⟨a, f⟩ := g x; dsimp
  refine Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => ?_
  <;> rfl

def toLast {α} (x : P α) : P.last (α .fz) where
  fst := x.1
  snd := x.2 .fz

theorem bisim_map {α}
    {a b : M.{u} P α}
    (R : M.{u} P α → M.{u} P α → Prop)
    (x : R a b)
    (h : ∀ s t, R s t →
      ∃ (x : (TypeVec.id ::: Function.const _ PUnit.unit) <$$> s.dest
        = (TypeVec.id ::: Function.const _ PUnit.unit) <$$> t.dest),
        ∀ v, R
          (s.dest.snd .fz v)
          <| t.dest.snd .fz
          <| cast (congr (congr rfl (Sigma.ext_iff.mp x).1) rfl) v)
    : a = b := by
  rcases a with ⟨a, afn⟩
  rcases b with ⟨b, bfn⟩
  obtain rfl : a = b :=
    Uni.M.bisim (fun a b => ∃ af bf, R ⟨a, af⟩ ⟨b, bf⟩)
      ⟨_, _, x⟩
      <| by
    clear a b afn bfn x
    intro a b ⟨af, bf, r⟩
    dsimp
    have ⟨hf, hrst⟩ := h _ _ r
    refine ⟨?_, ?_⟩
    · change toLast ((TypeVec.id ::: Function.const (M P α) PUnit.unit) <$$> M.dest ⟨a, af⟩) = _
      rw [hf]
      rfl
    · refine fun v => ⟨_, _, hrst v⟩
  refine Sigma.ext rfl <| heq_of_eq ?_
  funext i v
  dsimp at v ⊢
  induction v
  case root x' a f h' j c =>
    cases x' using Uni.M.mk_cases
    simp only [Uni.M.mk_dest] at h'
    subst h'
    have ⟨tf, ts⟩ := h _ _ x
    have := funext_iff.mp (eq_of_heq (Sigma.ext_iff.mp tf).2) j.fs
    dsimp [M.dest, M.dest', ] at this
    have := funext_iff.mp this (cast (by simp) c)
    simp only [M.pathDestLeft] at this
    rewrite! [Uni.M.mk_dest] at this
    exact this
  case child x' a f h' v j c ih =>
    cases x' using Uni.M.mk_cases
    simp only [Uni.M.mk_dest] at h'
    subst h'
    apply ih
    have ⟨_, ts⟩ := h _ _ x
    dsimp at ts
    specialize ts (cast (by simp [M.dest, M.dest']; rfl) v)
    simp only [M.dest, M.dest', Nat.succ_eq_add_one, TypeVec.drop_append1_simp, TypeVec.last_eq,
      TypeVec.splitFun.get_fz] at ts
    rewrite! [Uni.M.mk_dest] at ts
    exact ts


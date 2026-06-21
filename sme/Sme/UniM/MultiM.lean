import Sme.AltRepr
import Sme.HEq
import Sme.UniM.HpLuM
import Sme.PFunctor.Utils
import Sme.ForMathlib.Data.TypeVec
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

namespace M

@[reducible]
instance : MvFunctor (M P) := by
  change MvFunctor (mp P)
  infer_instance

/- instance {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin2 n, Inhabited (α i)]  -/
/-     : Inhabited (P.M α) := -/
/-   @Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _ -/

/-- construct through corecursion the shape of an M-type
without its contents -/
def corecShape {β : Type v} (g₀ : β → P.A) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) :
    β → Uni.M P.last :=
  Uni.M.corec fun b => ⟨g₀ b, g₂ b⟩

open scoped MvFunctor

/-- Proof of type equality as an arrow -/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' := fun _i b => Eq.recOn h b

/-- Proof of type equality as a function -/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' := fun b => Eq.recOn h b

/-- Using corecursion, construct the contents of an M-type -/
def corecContents {α : TypeVec.{u} n}
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
def corecBase
    {α : TypeVec n} {β : Type w} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (b : β)
    : M P α where
  fst := corecShape P g₀ g₂ b
  snd := M.corecContents P g₀ g₁ g₂ _ _ rfl

variable {P}

/-- Corecursor for M-type of `P` -/
def corec' {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) : β → M P α :=
  M.corecBase P
    (fun b => (g b).fst)
    (fun b => TypeVec.dropFun (g b).snd)
    (fun b => TypeVec.lastFun (g b).snd)

def corec {α : TypeVec n} {β : Type v}
    (gen : β → P.uLift (α.uLift.append1 (ULift.{u} β))) : β → M P α :=
  M.corecBase P
    (gen · |>.fst.down)
    (gen · |>.snd |> TypeVec.dropFun |>.uLift_arrow)
    (fun x => (.up · |> (gen x |>.snd |> TypeVec.lastFun) |>.down))

/-- Implementation of destructor for M-type of `P` -/
def pathDestLeft {α : TypeVec n} {x : Uni.M P.last} {a : P.A} {f : P.last.B a → Uni.M P.last}
    (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c =>
  f' i (M.Path.root x a f h i c)

/-- Implementation of destructor for M-type of `P` -/
def pathDestRight {α : TypeVec n} {x : Uni.M P.last} {a : P.A} {f : P.last.B a → Uni.M P.last}
    (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α)
    (j : P.last.B a)
    : M.Path P (f j) ⟹ α := fun i c => f' i (M.Path.child x a f h j i c)

/-- Destructor for M-type of `P` -/
def dest' {α : TypeVec n} {x : Uni.M P.last} {a : P.A} {f : P.last.B a → Uni.M P.last}
    (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P (α.append1 (M P α)) :=
  ⟨a, TypeVec.splitFun (M.pathDestLeft h f') fun x => ⟨f x, M.pathDestRight h f' x⟩⟩

/-- Destructor for M-types -/
def dest {α : TypeVec n} (x : M P α) : P (α ::: M P α) :=
  M.dest'
    (Sigma.eta <| (x.fst).dest).symm
    x.snd

/-- Constructor for M-types -/
def mk {α : TypeVec n} : P (α.append1 (M P α)) → M P α :=
  M.corec' fun i => TypeVec.appendFun TypeVec.id dest <$$> i

theorem dest'_eq_dest' {α : TypeVec n} {x : Uni.M P.last} {a₁ : P.A}
    {f₁ : P.last.B a₁ → Uni.M P.last} (h₁ : x.dest = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.last.B a₂ → Uni.M P.last} (h₂ : x.dest = ⟨a₂, f₂⟩) (f' : M.Path P x ⟹ α) :
    M.dest' h₁ f' = M.dest' h₂ f' := by cases h₁.symm.trans h₂; rfl

theorem dest_eq_dest' {α : TypeVec n} {x : Uni.M P.last} {a : P.A}
    {f : P.last.B a → Uni.M P.last} (h : x.dest = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    M.dest ⟨x, f'⟩ = M.dest' h f' :=
  dest'_eq_dest' _ _ _

theorem dest_corecBase {α : TypeVec.{u} n} {β : Type v} (g₀ : β → P.A)
    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (x : β)
    : M.dest
      (M.corecBase P g₀ g₁ g₂ x)
    = ⟨g₀ x, TypeVec.splitFun (g₁ x) (M.corecBase P g₀ g₁ g₂ ∘ g₂ x)⟩ :=by
  simp only [Nat.succ_eq_add_one, dest, dest', corecBase, TypeVec.drop_append1_simp,
    TypeVec.last_eq, TypeVec.append1_get_fz]
  simp only [corecShape]
  rw! [Uni.M.dest_corec]
  refine Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => ?_
  <;> rfl

@[simp]
theorem dest_corec' {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) (x : β) 
    : M.dest (M.corec' g x) = TypeVec.appendFun TypeVec.id (M.corec' g) <$$> g x := by
  trans
  · apply M.dest_corecBase
  have ⟨a, f⟩ := g x; dsimp
  refine Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs _ => ?_
  <;> rfl

open scoped TypeVec

@[simp]
theorem dest_corec {α : TypeVec n} {β : Type v}
    (g : β → P.uLift (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    (x : β) :
    M.dest (M.corec g x)
    = (P.uLift_down <|
        (TypeVec.Arrow.uLift_up ⊚ (TypeVec.Arrow.uLift_down ::: (M.corec g ·.down)))
          <$$> g x) := by
  trans
  · apply M.dest_corecBase
  refine Sigma.ext rfl <| heq_of_eq ?_
  dsimp
  funext i v
  rcases i with (_|_)
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
    Uni.M.bisim (∃ af bf, R ⟨·, af⟩ ⟨·, bf⟩)
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

variable {α : TypeVec _}

@[simp]
theorem dest_map
    {α β : TypeVec.{u} n} (g : α ⟹ β) (x : M P α)
    : dest (g <$$> x) = (g ::: (g <$$> ·)) <$$> dest x := by
  simp only [Nat.succ_eq_add_one, id_eq, MvFunctor.map, map]
  refine Sigma.ext (by rfl) <| heq_of_eq ?_
  funext i h
  rcases i with (_|_) <;> rfl

theorem map_corec {γ : Type v} {β : TypeVec n} {f : α ⟹ β}
    {gen : γ → uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} γ)} {g : γ}
    : f <$$> corec gen g = corec ((TypeVec.Arrow.arrow_uLift f ::: id) <$$> gen ·) g := by
  apply bisim_map
    (∃ y, f <$$> corec gen y = · ∧ corec ((TypeVec.Arrow.arrow_uLift f ::: id) <$$> gen ·) y = ·)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨w, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, id_eq, map_fst, cast_eq, dest_map, dest_corec, uLift_down,
    map_snd, map_mk, exists_prop]
  refine ⟨Sigma.ext rfl <| heq_of_eq ?_, ?_⟩
  · ext (_|_) h <;> rfl
  · intro v
    rw! (castMode := .all) [dest_map, dest_corec]
    dsimp
    refine ⟨_, rfl, ?_⟩
    symm
    rw! (castMode := .all) [dest_corec]
    dsimp
    rw [eqRec_eq_cast, eqRec_eq_cast]

theorem map_corec' {γ : Type u} {β : TypeVec n} {f : α ⟹ β}
    {gen : γ → P (α ::: γ)} {g : γ}
    : f <$$> corec' gen g = corec' ((f ::: id) <$$> gen ·) g := by
  apply bisim_map
    (∃ y, f <$$> corec' gen y = · ∧ corec' ((f ::: id) <$$> gen ·) y = ·)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨w, rfl, rfl⟩
  simp only [Nat.succ_eq_add_one, id_eq, map_fst, cast_eq, dest_map, dest_corec', exists_prop]
  constructor
  · simp [MvPFunctor.map_map, TypeVec.appendFun_comp']
  · intro v
    rw! (castMode := .all) [dest_map, dest_corec']
    simp only [Nat.succ_eq_add_one, id_eq, map_snd, map_fst, TypeVec.comp.get,
      TypeVec.append1_get_fz, TypeVec.appendFun.get_fz, Function.comp_apply]
    refine ⟨_, rfl, ?_⟩
    symm
    rw! (castMode := .all) [dest_corec']
    dsimp
    rw [eqRec_eq_cast, eqRec_eq_cast]

@[simp]
theorem dest_mk {v : M P α} : mk (dest v) = v := by
  apply bisim_map (· = (mk ∘ dest) ·) rfl
  rintro _ x rfl
  simp only [Nat.succ_eq_add_one, Function.comp_apply, map_fst]
  constructor
  case w =>
    simp [mk, MvPFunctor.map_map, TypeVec.appendFun_comp']
  · intro v
    simp only [mk, Nat.succ_eq_add_one]
    rw! (castMode := .all) [dest_corec']
    rfl

@[ext]
theorem ext_dest {α : TypeVec n} {x y : M P α} (h : x.dest = y.dest) : x = y := by
  rw [← dest_mk (v := x), h, dest_mk]

@[elab_as_elim]
theorem mk_cases {motive : M P α → Prop}
    (h : ∀ v, motive (.mk v))
    v
    : motive v := by
  rw [←dest_mk (v := v)]
  exact h v.dest

@[simp]
theorem mk_dest {v : P (α ::: M P α)} : dest (mk v) = v := by
  have : mk ∘ dest = @id (M P α) := funext fun x => dest_mk
  rw [mk, dest_corec', ←mk, ←comp_map]
  refine Sigma.ext rfl <| heq_of_eq ?_
  dsimp only [map_fst, map_snd]
  funext i h
  rcases i with (_|i)
  · change (mk ∘ dest) _ = id _
    rw [this]
  · rfl

theorem map_mk
    {α β : TypeVec.{u} n} (g : α ⟹ β) (x : P (α ::: M P α))
    : g <$$> mk x = mk ((g ::: (MvFunctor.map g)) <$$> x) := by
  ext
  simp

theorem corec_roll
    {α : TypeVec.{u} n}
    {X : Type v}
    {Y : Type w} {x₀ : X}
    (f : X → Y)
    (g : Y → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} X))
    : corec (g ∘ f) x₀ = corec (transliterateMap (ULift.up ∘ f ∘ ULift.down) ∘ g) (f x₀) := by
  apply bisim_map
    (∃ x, corec (g ∘ f) x = · ∧ corec (transliterateMap (ULift.up ∘ f ∘ ULift.down) ∘ g) (f x) = ·)
    ⟨_, rfl, rfl⟩
  rintro _ _ ⟨w, rfl, rfl⟩
  rw [dest_corec, dest_corec]
  simp only [Nat.succ_eq_add_one, Function.comp_apply, uLift_down_fst, map_fst, uLift_down_snd,
    map_snd, TypeVec.uLift_arrow.get, TypeVec.append1_get_fz, TypeVec.comp.get,
    TypeVec.uLift_up.get, TypeVec.appendFun.get_fz, transliterateMap_fst, ULift.transliterate_down,
    cast_eq, exists_prop]
  refine ⟨Sigma.ext rfl <| heq_of_eq <| funext₂ fun | .fz, h | .fs _, _ => rfl, ?_⟩
  intro v
  refine ⟨_, rfl, rfl⟩


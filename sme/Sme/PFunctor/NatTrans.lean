import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite

namespace MvPFunctor

open scoped MvFunctor

universe u

variable {n : Nat}

/-- A natural transformation over polynomial functors.
This is comprised of a forward map on positions,
and a backwards map on directions.
This is equivalent to the notion of a natural transformation in Cat,
this can be seen in `f` and `nat`.

The reason we store it as a forward map and backward map is twofold:
1. We get signifigantly more defeqs,
2. it makes the category small.
For a view on how it was with the other defn see bf07af82f1a1f37c1b011c21d0365cf50834127f,
in my diss repository.
-/
structure NatTrans (P Q : MvPFunctor.{u} n) : Type u where
  mkOfHdChild ::
  hd : P.A → Q.A
  child x : Q.B (hd x) ⟹ P.B x

namespace NatTrans

variable {P Q R : MvPFunctor n}

theorem nt_fst_eq
    (f : ∀ α, P α → Q α)
    (nat : (α β m x : _) → m <$$> f α x = f β (m <$$> x))
    {α β}
    {x : P α} {y : P β} (h : x.fst = y.fst)
    : (f _ x).fst = (f _ y).fst := by
  rcases x with ⟨x,x₁⟩
  rcases y with ⟨_,y₁⟩
  subst h
  rw [←MvPFunctor.map_fst (α := α) (arr := fun _ _ => PUnit.unit), nat]
  rw [←MvPFunctor.map_fst (α := β) (arr := fun _ _ => PUnit.unit), nat]
  rfl

@[simp]
theorem nt_fst_eq_hd
    (f : ∀ α, P α → Q α)
    (nat : (α β m x : _) → m <$$> f α x = f β (m <$$> x))
    {α x}
    : (f α x).fst = (f (fun _ => PUnit) ⟨x.1, fun _ _ => .unit⟩).fst :=
  nt_fst_eq f nat rfl

def mk
    (f : ∀ α, P α → Q α)
    (nat : (α β m x : _) → m <$$> f α x = f β (m <$$> x))
    : NatTrans P Q where
  hd v := (f (fun _ => PUnit) ⟨v, fun _ _ => .unit⟩).fst
  child b i v := (f (P.B b) ⟨b, TypeVec.id⟩).snd i (cast (by
      congr 1
      exact nt_fst_eq f nat rfl
    ) v)

def f (nt : NatTrans P Q) α
    (pre : P α)
    : Q α where
  fst := nt.hd pre.1
  snd := pre.2 ⊚ nt.child pre.1

theorem nat
    (nt : NatTrans P Q)
    {α β}
    {m x}
    : m <$$> nt.f α x = nt.f β (m <$$> x) := rfl

instance : CoeFun (NatTrans P Q) (fun _ => ∀ {α}, P α → Q α) where coe := f

@[ext 900]
theorem ext {a b : NatTrans P Q}
    (h : a.f = b.f)
    : a = b := by
  rcases a with ⟨ha, _⟩; rcases b with ⟨hb, _⟩
  unfold NatTrans.f at h
  dsimp only at h
  obtain rfl : ha = hb := by
    funext i
    have := funext_iff.mp (funext_iff.mp h (P.B i)) ⟨i, TypeVec.id⟩
    simp only [TypeVec.id_comp, Sigma.mk.injEq] at this
    exact this.1
  simp only [mkOfHdChild.injEq, heq_eq_eq, true_and]
  funext v
  simpa using funext_iff.mp (funext_iff.mp h (P.B v)) ⟨v, TypeVec.id⟩

@[ext]
theorem ext' {a b : NatTrans P Q}
    (h : ∀ hd, a.f _ ⟨hd, TypeVec.id⟩ = b.f _ ⟨hd, TypeVec.id⟩)
    : a = b := by
  ext α ⟨hd, tl⟩
  change a.f _ (tl <$$> ⟨hd, TypeVec.id⟩) = b.f _ (tl <$$> ⟨hd, TypeVec.id⟩)
  rw [←a.nat, ←b.nat, h]

def id (P : MvPFunctor n) : NatTrans P P where
  hd := _root_.id
  child _ := TypeVec.id
abbrev id' {P : MvPFunctor n} : NatTrans P P := id P
def comp (u : NatTrans P Q) (v : NatTrans Q R) : NatTrans P R where
  hd := v.hd ∘ u.hd
  child _ := u.child _ ⊚ v.child _
  /- f α x := v.f _ (u.f _ x) -/
  /- nat α β m x := calc -/
  /-   m <$$> v.f α (u.f α x) -/
  /-     = v.f β (m <$$> (u.f _ x)) := by rw [v.nat] -/
  /-   _ = v.f β (u.f β (m <$$> x)) := by rw [u.nat] -/

@[simp]
theorem comp_hd
    {u : NatTrans P Q} {v : NatTrans Q R}
    : (u.comp v).hd = (v.hd ∘ u.hd) := rfl

theorem child_eq
    {f g : NatTrans P Q}
    {b : P.A} {i}
    {x y}
    {α} (tl : P.B b ⟹ α)
    (h : f.child b i x = g.child b i y)
    : (f.f α ⟨b, tl⟩).snd i x
    = (g.f α ⟨b, tl⟩).snd i y := by
  rcases f with ⟨hf, cf⟩
  rcases g with ⟨hg, cg⟩
  simp_all [f]

theorem rev
    {v : NatTrans Q R}
    {α x i u}
    : (v.f α x).snd i u
    = x.snd i (v.child x.1 i u) :=
  rfl

theorem comp_child
    {u : NatTrans P Q} {v : NatTrans Q R} {i b x}
    : u.child b i (v.child (u.hd b) i x) = (u.comp v).child b i x :=
  rfl

theorem comp_child'
    {u : NatTrans P Q} {v : NatTrans Q R}
    : (u.comp v).child = (fun b => (u.child b) ⊚ (v.child (u.hd b))) :=
  rfl

theorem nt_snd_eq_child
    {v : NatTrans Q R}
    {α x}
    : (v.f α x).snd
    = x.snd ⊚ (v.child x.1) :=
  rfl

@[simp]
theorem transform_mk
    {v : NatTrans Q R}
    {α hd tl}
    : v.f α ⟨hd, tl⟩ = ⟨v.hd hd, tl ⊚ v.child hd⟩ :=
  rfl

@[simp]
theorem hd_mkOfHdChild
    (pos : P.A → Q.A)
    (dir : ∀ hd, Q.B (pos hd) ⟹ P.B hd)
    : (mkOfHdChild pos dir).hd = pos := rfl

@[simp]
theorem child_mkOfHdChild
    (pos : P.A → Q.A)
    (dir : ∀ hd, Q.B (pos hd) ⟹ P.B hd)
    : (mkOfHdChild pos dir).child = dir := rfl

@[simp]
theorem mkOfHdChild_eta
    {x : NatTrans P Q}
    : (mkOfHdChild x.hd x.child) = x :=
  rfl

@[ext 850]
theorem ext_hd_child {a b : NatTrans P Q}
    (hhd : a.hd = b.hd)
    (hch : a.child ≍ b.child)
    : a = b := by
  cases a; next ah ac =>
  cases b; next bh bc =>
  obtain rfl : ah = bh := hhd
  dsimp at hch
  subst hch
  rfl

end NatTrans


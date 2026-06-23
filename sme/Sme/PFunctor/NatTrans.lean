import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite

namespace MvPFunctor

open scoped MvFunctor

universe u

variable {n : Nat}

structure NatTrans (P Q : MvPFunctor.{u} n) where
  mk ::
  f : ∀ α, P α → Q α
  nat α β (m : α ⟹ β) (x : P α) : m <$$> (f α x) = f β (m <$$> x)

namespace NatTrans

variable {P Q R : MvPFunctor n}

instance : CoeFun (NatTrans P Q) (fun _ => ∀ {α}, P α → Q α) where coe := f

@[ext 900]
theorem ext {a b : NatTrans P Q}
    (h : a.f = b.f)
    : a = b := by
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  subst h
  rfl

@[ext]
theorem ext' {a b : NatTrans P Q}
    (h : ∀ hd, a.f _ ⟨hd, TypeVec.id⟩ = b.f _ ⟨hd, TypeVec.id⟩)
    : a = b := by
  ext α ⟨hd, tl⟩
  change a.f _ (tl <$$> ⟨hd, TypeVec.id⟩) = b.f _ (tl <$$> ⟨hd, TypeVec.id⟩)
  rw [←a.nat, ←b.nat, h]


def id (P : MvPFunctor n) : NatTrans P P := ⟨fun _ x => x, fun _ _ _ _ => rfl⟩
abbrev id' {P : MvPFunctor n} : NatTrans P P := id P
def comp (u : NatTrans P Q) (v : NatTrans Q R) : NatTrans P R where
  f α x := v.f _ (u.f _ x)
  nat α β m x := calc
    m <$$> v.f α (u.f α x)
      = v.f β (m <$$> (u.f _ x)) := by rw [v.nat]
    _ = v.f β (u.f β (m <$$> x)) := by rw [u.nat]

def hd (nt : NatTrans P Q) (v : P.A) : Q.A :=
  (nt.f (fun _ => PUnit) ⟨v, fun _ _ => .unit⟩).fst

@[simp]
theorem comp_hd
    {u : NatTrans P Q} {v : NatTrans Q R}
    : (u.comp v).hd = (v.hd ∘ u.hd) := rfl

theorem nt_fst_eq (nt : NatTrans P Q) {α β}
    {x : P α} {y : P β} (h : x.fst = y.fst)
    : (nt.f _ x).fst = (nt.f _ y).fst := by
  rcases x with ⟨x,x₁⟩
  rcases y with ⟨_,y₁⟩
  subst h
  rw [←MvPFunctor.map_fst (α := α) (arr := fun _ _ => PUnit.unit), nt.nat]
  rw [←MvPFunctor.map_fst (α := β) (arr := fun _ _ => PUnit.unit), nt.nat]
  rfl

@[simp]
theorem nt_fst_eq_hd (nt : NatTrans P Q)
    {α x}
    : (nt.f α x).fst = nt.hd x.1 :=
  nt_fst_eq nt rfl

def child (nt : NatTrans P Q) (b : P.A) : Q.B (hd nt b) ⟹ P.B b := by
  refine fun i v => (nt.f (P.B b) ⟨b, TypeVec.id⟩).snd i (cast (?_) v)
  congr 2
  refine nt_fst_eq nt rfl

theorem child_eq
    {f g : NatTrans P Q}
    {b : P.A} {i}
    {x y}
    {α} (tl : P.B b ⟹ α)
    (h : f.child b i x = g.child b i y)
    : (f.f α ⟨b, tl⟩).snd i (cast (by simp) x)
    = (g.f α ⟨b, tl⟩).snd i (cast (by simp) y) := by
  simp [child] at h
  change (f.f α (tl <$$> ⟨b, TypeVec.id⟩)).snd i _ = (g.f α (tl <$$> ⟨b, TypeVec.id⟩)).snd i _
  rw! (castMode := .all) [←f.nat _ _ tl ⟨b, TypeVec.id⟩, ←g.nat _ _ tl ⟨b, TypeVec.id⟩]
  simp [eqRec_eq_cast, h]

theorem rev
    {v : NatTrans Q R}
    {α x i u}
    : (v.f α x).snd i u
    = x.snd i (v.child x.1 i (cast (by congr 1; simp) u)) := by
  rcases x with ⟨hd, tl⟩
  change (v.f α (tl <$$> ⟨hd, TypeVec.id⟩)).snd i u = _
  rw! (castMode := .all) [←v.nat]
  simp [map_mk, TypeVec.comp_id, eqRec_eq_cast, map_fst, map_snd, TypeVec.comp.get,
    Function.comp_apply, child]

theorem comp_child
    {u : NatTrans P Q} {v : NatTrans Q R} {i b x}
    : u.child b i (v.child (u.hd b) i x) = (u.comp v).child b i x := by
  symm
  unfold comp child
  dsimp
  rw [rev]
  simp only [cast_cast]
  congr!
  change v.child _ _ _ = _
  rw! [u.nt_fst_eq_hd]
  rfl

theorem comp_child'
    {u : NatTrans P Q} {v : NatTrans Q R}
    : (u.comp v).child = (fun b => (u.child b) ⊚ (v.child (u.hd b))) := by
  funext i b x
  rw [←comp_child]
  rfl

theorem nt_snd_eq_child
    {v : NatTrans Q R}
    {α x}
    : (v.f α x).snd
    = x.snd ⊚ (v.child x.1) ⊚ (.mp <| by simp) := by
  funext i h
  simp [rev]

theorem transform_mk
    {v : NatTrans Q R}
    {α hd tl}
    : v.f α ⟨hd, tl⟩ = ⟨v.hd hd, tl ⊚ v.child hd⟩ := by
  change v.f α (tl <$$> ⟨hd, TypeVec.id⟩) = tl <$$> ⟨v.hd hd, v.child hd⟩
  rw [←v.nat]
  congr
  apply Sigma.ext
  · simp
  · simp only [nt_snd_eq_child, TypeVec.id_comp]
    rw [TypeVec.heq_of_mp_mpr rfl (by simp)]
    simp

def mkOfHdChild
    (pos : P.A → Q.A)
    (dir : ∀ hd, Q.B (pos hd) ⟹ P.B hd)
    : NatTrans P Q where
  f := fun _ x => ⟨pos x.1, x.2 ⊚ dir _⟩
  nat _ _ _ _ := rfl

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
    : (mkOfHdChild x.hd x.child) = x := by
  ext i
  simp only [mkOfHdChild, transform_mk, TypeVec.id_comp]
  rfl

@[elab_as_elim]
def cases
    {motive : NatTrans P Q → Sort _}
    (h : ∀ pos dir, motive (mkOfHdChild pos dir))
    x : motive x :=
  cast (by rw [mkOfHdChild_eta]) (h x.hd x.child)

@[ext 850]
theorem ext_hd_child {a b : NatTrans P Q}
    (hhd : a.hd = b.hd)
    (hch : a.child ≍ b.child)
    : a = b := by
  cases a using cases; next ah ac =>
  cases b using cases; next bh bc =>
  obtain rfl : ah = bh := hhd
  dsimp at hch
  subst hch
  rfl

end NatTrans


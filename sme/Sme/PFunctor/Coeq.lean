import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite

namespace MvPFunctor

open scoped MvFunctor

universe u

variable {n : Nat}

structure NatTrans (P Q : MvPFunctor n) where
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

end NatTrans

abbrev coeq.r {P Q : MvPFunctor n} (f g : NatTrans P Q) : Q.A → Q.A → Prop :=
  (∃ x, · = g.hd x ∧ · = f.hd x)

def coeq {P Q : MvPFunctor n}
    (f g : NatTrans P Q)
    : MvPFunctor n where
  A := Quot (coeq.r f g)
  B e i :=
    { c : ∀ d, Quot.mk _ d = e → Q.B d i //
      ∀ b, ∀ h : Quot.mk _ (f.hd b) = e,
        f.child b i (c (f.hd b) h) =
        g.child b i (c (g.hd b) <| by
          subst h
          apply Quot.sound ⟨_, rfl, rfl⟩
        )
    }

namespace coeq

variable {P Q R : MvPFunctor n} (f g : NatTrans P Q)

def mk : NatTrans Q (coeq f g) where
  f _ v := ⟨Quot.mk _ v.1, fun i b => v.2 i <| b.1 _ rfl⟩
  nat _ _ _ _ := rfl

variable {f g : NatTrans P Q}

theorem mk_f_mk_g : f.comp (mk f g) = g.comp (mk f g) := by
  apply NatTrans.ext; funext α ⟨hd, tl⟩
  simp only [NatTrans.comp, mk]
  have : Quot.mk (r f g) (g.f α ⟨hd, tl⟩).fst = Quot.mk (r f g) (f.f α ⟨hd, tl⟩).fst :=
    Quot.sound <| ⟨hd, NatTrans.nt_fst_eq _ rfl, NatTrans.nt_fst_eq _ rfl⟩
  rw! (castMode := .all) [this]
  refine Sigma.ext_iff.mpr ⟨rfl, heq_of_eq <| funext₂ fun i ⟨v, p⟩ => ?_⟩
  dsimp
  rw! (castMode := .all) [NatTrans.nt_fst_eq_hd f, NatTrans.nt_fst_eq_hd g]
  simp only [eqRec_eq_cast]
  exact NatTrans.child_eq tl (p hd (by simp))

def lift
    (x : NatTrans Q R)
    (h : f.comp x = g.comp x)
    : NatTrans (coeq f g) R where
  f α v := by
    refine ⟨v.1.lift x.hd ?_,
      fun i hv => v.snd i ⟨fun d hz => x.child d i (cast (by rw [←hz]) hv),?_⟩⟩
    · rintro _ _ ⟨w, rfl, rfl⟩
      change (g.comp x).hd w = (f.comp x).hd w
      rw [h]
    · intro b h'
      dsimp [coeq]
      rw [NatTrans.comp_child, NatTrans.comp_child]
      rw! (castMode := .all) [h]
      simp [eqRec_eq_cast]
  nat _ _ _ _ := rfl

theorem unique (x : NatTrans Q R) (h : f.comp x = g.comp x)
    : (mk f g).comp (lift x h) = x := by
  ext hd
  simp [NatTrans.comp, lift, mk, NatTrans.transform_mk]
  rfl

end coeq

end MvPFunctor


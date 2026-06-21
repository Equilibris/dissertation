import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite
import Mathlib.Order.Extension.Linear

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

end NatTrans -------------------------------------------------------------------

def prod (P Q : MvPFunctor.{u} n) : MvPFunctor n where
  A := P.1 × Q.1
  B p i := P.2 p.1 i ⊕ Q.2 p.2 i

namespace prod

variable {P Q : MvPFunctor n}

def fst : NatTrans (prod P Q) P where
  f _ x := ⟨x.1.1, fun i => x.2 i ∘ .inl⟩
  nat _ _ _ _ := rfl

def snd : NatTrans (prod P Q) Q where
  f _ x := ⟨x.1.2, fun i => x.2 i ∘ .inr⟩
  nat _ _ _ _ := rfl

def mk {R} (f : NatTrans R P) (g : NatTrans R Q) : NatTrans R (prod P Q) where
  f _ x :=
    have fx := f _ x
    have gx := g _ x
    ⟨⟨fx.1, gx.1⟩, fun i v => v.elim (fx.2 i) (gx.2 i)⟩
  nat _ _ _ _ := by
    stop
    dsimp
    refine Sigma.ext rfl sorry
    simp
    sorry

theorem fst_mk {R} {f : NatTrans R P} {g : NatTrans R Q}
    : ((mk f g).comp fst) = f := rfl
theorem snd_mk {R} {f : NatTrans R P} {g : NatTrans R Q}
    : ((mk f g).comp snd) = g := rfl

def map {P' Q'} (f : NatTrans P' P) (g : NatTrans Q' Q) : NatTrans (prod P' Q') (prod P Q) :=
  mk (fst.comp f) (snd.comp g)

theorem fst_map {P' Q'} {f : NatTrans P' P} {g : NatTrans Q' Q}
    : ((map f g).comp fst) = fst.comp f := rfl
theorem snd_map {P' Q'} {f : NatTrans P' P} {g : NatTrans Q' Q}
    : ((map f g).comp snd) = snd.comp g := rfl

end prod

abbrev coeq.r {P Q : MvPFunctor n} (f g : NatTrans P Q) : Q.A → Q.A → Prop :=
  (∃ x, · = g.hd x ∧ · = f.hd x)
  /- (fun a b => ∃ x, a = g.hd x ∧ b = f.hd x) -/

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

namespace coeq -----------------------------------------------------------------

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


-- False
def dist
    {P' Q' : MvPFunctor.{u} _}
    {f' g' : NatTrans P' Q'}
    : NatTrans (prod (coeq f g) (coeq f' g')) (coeq (prod.map f f') (prod.map g g')) where
  f α v := by
    refine ⟨
      Quot.lift₂ (Quot.mk _ ⟨·, ·⟩) ?_ ?_ v.1.1 v.1.2,
      fun a b => by
        apply v.2
        dsimp [coeq, prod]
        sorry
    ⟩
    stop
    sorry
  nat := sorry

-- False
def lift₂
    {P Q P' Q' : MvPFunctor.{u} _}
    {f g : NatTrans P Q}
    {f' g' : NatTrans P' Q'}
    (x : NatTrans (prod Q Q') R)
    (h₁ : (prod.map f .id').comp x = (prod.map g .id').comp x)
    (h₂ : (prod.map .id' f').comp x = (prod.map .id' g').comp x)
    : NatTrans (prod (coeq f g) (coeq f' g')) R where
  f α v := by
    have := x.hd
    refine ⟨Quot.lift₂ (x.hd ⟨·, ·⟩) ?_ ?_ v.1.1 v.1.2,
      fun i hv =>
        have := x.child sorry
        v.snd i (by sorry)
    ⟩
    stop
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

theorem ind {Z} {a b : NatTrans (coeq f g) Z}
    (h : (mk f g).comp a = (mk f g).comp b)
    : a = b := by
  cases a using NatTrans.cases; next ap ad =>
  cases b using NatTrans.cases; next bp bd =>
  obtain rfl : ap = bp := by
    obtain ⟨h', -⟩ := NatTrans.ext_hd_child_iff.mp h
    dsimp at h'
    funext hd
    cases hd using Quot.ind; next hd =>
    exact funext_iff.mp h' hd
  refine NatTrans.ext_hd_child (by rfl) <| heq_of_eq ?_
  dsimp
  obtain ⟨-, h'⟩ := NatTrans.ext_hd_child_iff.mp h
  simp only [NatTrans.comp_hd, NatTrans.hd_mkOfHdChild, Function.comp_apply, NatTrans.comp_child',
    NatTrans.child_mkOfHdChild, heq_eq_eq] at h'
  ext a i z
  apply Subtype.ext
  cases a using Quot.ind; next a =>
  ext qz v
  have : _ = _ := funext_iff.mp (funext_iff.mp (funext_iff.mp h' qz) i) (cast (by 
    rw [←v];rfl) z)
  dsimp [mk, NatTrans.child, NatTrans.hd, Function.comp] at this
  rewrite! (castMode := .all) [v, v] at this
  exact this

theorem mk_sur
    {α}
    [hne : ∀ i, Nonempty (α i)]
    (hf : ∀ h i, Function.Injective (f.child h i))
    (hg : ∀ h i, Function.Injective (g.child h i))
    : Function.Surjective (mk f g α) := by
  rintro ⟨⟨hd⟩, ch⟩
  conv => rhs; intro x; rw [Sigma.ext_iff]
  dsimp [mk]
  use ⟨hd, fun i x => by
    by_cases h : ∃ b : (coeq f g).B (Quot.mk (r f g) hd) i, b.1 hd rfl = x
    · exact ch i h.choose
    · exact (hne i).some
    ⟩
  simp only [heq_eq_eq, true_and]
  funext i b
  split <;> rename_i h
  · suffices h : h.choose = b by rw [h]
    apply Subtype.ext
    ext a w
    have := h.choose_spec
    sorry
  · 
    sorry

theorem ind' {α}
    {motive : coeq f g α → Prop}
    (h : ∀ p, motive (mk f g _ p))
    x : motive x := by
  rcases x with ⟨xf, xs⟩
  cases xf using Quot.ind; next xf =>
  dsimp [mk] at h
  have := h ⟨xf, xs ⊚ fun i x => ⟨fun d h => 
    sorry, sorry⟩⟩
  dsimp at this
  sorry

def toQuotient {R : (α : _) → Q α → Q α → Prop}
    (cohere : ∀ α a b, Relation.EqvGen (∃ x, f α x = · ∧ g α x = ·) a b = R α a b)
    (nat : ∀ α β f a b, R α a b → R β (f <$$> a) (f <$$> b))
    (equiv : ∀ α, Equivalence (R α))
    {α}
    (x : coeq f g α)
    : Quotient ⟨R α, equiv α⟩ :=
  have ⟨h, c⟩ := x
  Quot.hrecOn h (motive := fun _ => Quotient ⟨R α, equiv α⟩)
    (fun hd =>
      Quotient.mk ⟨R α, equiv α⟩ ⟨
        hd,
        fun i rs => by
          have := x.snd i ⟨
            sorry,
            sorry
          ⟩
          /- dsimp [coeq] at this -/
          sorry
      ⟩
    )
    sorry
  /- by -/
  /- sorry -/

theorem mk_eq_iff' {α} {a b : Q α}
    (h : mk f g α a = mk f g α b)
    : Relation.EqvGen (∃ x, f α x = · ∧ g α x = ·) a b := by
  rcases a with ⟨af, as⟩
  rcases b with ⟨bf, bs⟩
  dsimp [mk] at h
  have ⟨ha, hb⟩ := Sigma.ext_iff.mp h; clear h
  dsimp at ha hb
  induction Quot.eq.mp ha <;> clear ha
  case rel h =>
    rcases h with ⟨x, rfl, rfl⟩
    refine Relation.EqvGen.symm _ _ <| Relation.EqvGen.rel _ _ ?_
    have := f.child x
    use ⟨x, sorry⟩
    rw [NatTrans.transform_mk, NatTrans.transform_mk, Sigma.ext_iff, Sigma.ext_iff]
    simp only [heq_eq_eq, true_and]
    sorry
  · rw [heq_eq_eq] at hb
    suffices h : as = bs by
      subst h
      exact .refl _
    funext i x
    have := as i x
    have := funext_iff.mp (funext_iff.mp hb i) ⟨fun d heq => sorry, sorry⟩
    sorry
  · sorry
  · sorry

  stop
  rcases h with ⟨x, rfl, rfl⟩
  change (f.comp (mk f g)) α x = (g.comp (mk f g)) α x
  rw [mk_f_mk_g]

theorem mk_eq_iff {α} {a b : Q α}
    (h : ∃ x, f α x = a ∧ g α x = b)
    : mk f g α a = mk f g α b := by
  rcases h with ⟨x, rfl, rfl⟩
  change (f.comp (mk f g)) α x = (g.comp (mk f g)) α x
  rw [mk_f_mk_g]

section

variable {α : TypeVec 1}

def plist : MvPFunctor 1 := ⟨Nat, fun v _ => Fin v⟩

namespace plist

def nil : plist α := ⟨Nat.zero, fun _ n => n.elim0⟩
def cons (hd : α .fz) (tl : plist α) : plist α where
  fst := tl.1.succ
  snd := fun
    | .fz, ⟨0, p⟩ => hd
    | .fz, ⟨n+1, p⟩ => tl.2 .fz ⟨n, by omega⟩

def toList (l : plist α) : List (α .fz) := List.ofFn (l.snd .fz)
def ofList (l : List (α .fz)) : plist α where
  fst := l.length
  snd | .fz => ((l[·]) : Fin _ → _)

def length : NatTrans plist (const _ Nat) where
  f _ x := const.mk _ x.1
  nat _ _ _ _ := by simp

@[simp]
theorem toList_nil : toList (nil (α := α)) = [] := rfl
@[simp]
theorem toList_cons {hd} {tl : plist α} : toList (cons hd tl) = hd :: toList tl := by
  simp only [toList, cons, Nat.succ_eq_add_one, List.ofFn_succ, List.cons.injEq, List.ofFn_inj]
  refine ⟨rfl, funext fun _ => rfl⟩

#check List.pairwise_insertionSort
#check ofList ∘ List.insertionSort (· ≤ ·) ∘ toList

theorem toList_map {β} (f : α ⟹ β) (x : plist α)
    : toList (f <$$> x) = (toList x).map (f .fz) := by
  simp [toList]

@[simp]
theorem map_ofList {β} (f : α ⟹ β) (x : List (α .fz))
    : f <$$> (ofList x) = (ofList (x.map (f .fz))) := by
  simp only [ofList, Fin.getElem_fin, List.getElem_map]
  rw! (castMode := .all) [List.length_map]
  refine Sigma.ext rfl <| heq_of_eq ?_
  funext i x
  rcases i with (_|_|_)
  simp

@[simp]
theorem ofList_toList {x : List (α .fz)}
    : (toList (ofList x)) = x := by
  simp [toList, ofList]

@[simp]
theorem toList_ofList {x : plist α}
    : (ofList (toList x)) = x := by
  rcases x with ⟨xf, xs⟩
  simp only [ofList, toList, Fin.getElem_fin, List.getElem_ofFn]
  rw! (castMode := .all) [List.length_ofFn]
  refine Sigma.ext rfl <| heq_of_eq ?_
  funext i x
  rcases i with (_|_|_)
  simp

theorem ofList_cases {motive : plist α → Prop}
    (h : ∀ v, motive (ofList v))
    x : motive x := by
  rw [←toList_ofList (x := x)]
  exact h (toList x)

def equivList : plist α ≃ List (α .fz) where
  toFun := toList
  invFun := ofList
  left_inv x := by simp
  right_inv _ := by simp

end plist

def permlist
    : MvPFunctor 1 := ⟨
  (x : Nat) × Equiv.Perm (Fin x),
  fun ⟨v, _⟩ _ => Fin v
⟩

namespace permlist

def ofList (l : List (α .fz)) (perm : Equiv.Perm (Fin l.length)) : permlist α where
  fst := ⟨_, perm⟩
  snd | .fz => ((l[·]) : Fin _ → _)
/- permlist.proj.f α (permlist.ofList (plist.toList a) eq) -/

def proj : NatTrans permlist plist where
  f _ pls := ⟨pls.1.1, pls.2⟩
  nat a b f x := rfl

def transp : NatTrans permlist plist where
  f _ pls := ⟨pls.1.1, (fun a i => pls.2 _ (pls.1.2 i))⟩
  nat a b f x := rfl

@[simp]
theorem proj_ofList {l : List (α .fz)} {perm : Equiv.Perm (Fin l.length)}
    : proj α (ofList l perm) = plist.ofList l := by
  refine Sigma.ext rfl <| heq_of_eq ?_
  funext i x
  rcases i with (_|_|_)
  simp [proj, ofList, plist.ofList]

@[simp]
theorem transp_ofList {l : List (α .fz)} {perm : Equiv.Perm (Fin l.length)}
    : transp α (ofList l perm) = plist.ofList (List.ofFn ((l[·]) ∘ perm)) := by
  simp only [transp, ofList, Fin.getElem_fin, plist.ofList, List.getElem_ofFn, Function.comp_apply]
  rw! (castMode := .all) [List.length_ofFn]
  refine Sigma.ext rfl <| heq_of_eq ?_
  funext i x
  rcases i with (_|_|_)
  simp

end permlist

def multiset := coeq permlist.proj permlist.transp

def multiset.mk : NatTrans plist multiset := coeq.mk _ _

@[elab_as_elim]
theorem ofList_cases {A} {motive : List A → Prop}
    (hOfList : ∀ l : Nat, ∀ i : Fin l → A, motive (List.ofFn i))
    x : motive x := by
  rw [←List.ofFn_getElem (l := x)]
  apply hOfList

def fin_cast_equiv {a b : Nat}
    (h : a = b)
    : Fin a ≃ Fin b where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm

theorem perm_of_list_perm {A} {a b : List A} : List.Perm a b
    → ∃ p : (Equiv.Perm (Fin a.length)), b = List.ofFn ((a[·]) ∘ p.toFun)
  | .nil => ⟨⟨Fin.elim0, Fin.elim0, fun x => x.elim0, fun x => x.elim0⟩, by simp⟩
  | .trans x y => by
    have ⟨xeq, hx⟩ := perm_of_list_perm x
    have ⟨yeq, hy⟩ := perm_of_list_perm y
    subst hx
    subst hy
    use Equiv.trans (((fin_cast_equiv (by simp)).trans yeq).trans (fin_cast_equiv (by simp))) xeq
    cases a using ofList_cases; next la fa =>
    cases b using ofList_cases; next lb fb =>
    simp only [List.length_ofFn, Fin.getElem_fin, List.getElem_ofFn, Equiv.toFun_as_coe,
      Function.comp_apply, Fin.cast_mk, List.ofFn_inj] at *
    ext v
    simp [Equiv.trans_apply]
    rfl
  | .swap x y l => by
    use ⟨
      fun
        | ⟨0, h⟩ => ⟨1, Nat.one_lt_succ_succ l.length⟩
        | ⟨1, h⟩ => ⟨0, Nat.zero_lt_succ (x :: l).length⟩
        | ⟨n+2, h⟩ => ⟨n+2, h⟩,
      fun
        | ⟨0, h⟩ => ⟨1, Nat.one_lt_succ_succ l.length⟩
        | ⟨1, h⟩ => ⟨0, Nat.zero_lt_succ (x :: l).length⟩
        | ⟨n+2, h⟩ => ⟨n+2, h⟩,
      fun
        | ⟨0, h⟩ => rfl
        | ⟨1, h⟩ => rfl
        | ⟨n+2, h⟩ => rfl,
      fun
        | ⟨0, h⟩ => rfl
        | ⟨1, h⟩ => rfl
        | ⟨n+2, h⟩ => rfl,
    ⟩
    simp only [List.length_cons, Fin.getElem_fin, Fin.mk_one, Fin.zero_eta, List.ofFn_succ,
      Function.comp_apply, Fin.succ_zero_eq_one, List.cons.injEq]
    refine ⟨rfl, rfl, ?_⟩
    change l = List.ofFn fun i => l[i]
    simp only [Fin.getElem_fin, List.ofFn_getElem]
  | .cons x h => by
    have ⟨xeq, h⟩ := perm_of_list_perm h
    use ⟨
      fun
        | ⟨0, h⟩ => ⟨0, h⟩
        | ⟨n+1, h⟩ => Fin.succ (xeq ⟨n, Nat.succ_lt_succ_iff.mp h⟩),
      fun
        | ⟨0, h⟩ => ⟨0, h⟩
        | ⟨n+1, h⟩ => Fin.succ (xeq.invFun ⟨n, Nat.succ_lt_succ_iff.mp h⟩),
      fun
        | ⟨0, h⟩ => rfl
        | ⟨n+1, h⟩ => by simp [Fin.succ]
        ,
      fun
        | ⟨0, h⟩ => rfl
        | ⟨n+1, h⟩ => by simp [Fin.succ]
    ⟩
    subst h
    simp only [Fin.getElem_fin, Equiv.toFun_as_coe, List.length_cons, Fin.zero_eta, List.ofFn_succ,
      Function.comp_apply, List.cons.injEq, List.ofFn_inj]
    refine ⟨rfl, rfl⟩

theorem multiset.eq_mk {α a b}
    (h : (plist.toList a).Perm (plist.toList b))
    : multiset.mk α a = multiset.mk α b := by
  apply coeq.mk_eq_iff
  have ⟨eq, h⟩:= perm_of_list_perm h
  use permlist.ofList (plist.toList a) eq
  simp only [permlist.proj_ofList, plist.toList_ofList, permlist.transp_ofList, Fin.getElem_fin,
    true_and]
  cases b using plist.ofList_cases; next b =>
  cases a using plist.ofList_cases; next a =>
  apply (plist.equivList (α := α)).injective
  dsimp [plist.equivList]
  simp only [plist.ofList_toList]
  simp only [plist.ofList_toList, Fin.getElem_fin, Equiv.toFun_as_coe, Function.comp_apply] at h
  subst h
  rfl

theorem multiset.mk_eq {α a b}
    (h : multiset.mk α a = multiset.mk α b)
    : (plist.toList a).Perm (plist.toList b)
    := by
  simp only [mk, coeq.mk] at h
  rw [Sigma.ext_iff] at h
  dsimp at h
  sorry

example : multiset.mk (fun _ => Nat) (plist.cons 1 <| plist.cons 2 <| plist.nil)
    = multiset.mk _ (plist.cons 2 <| plist.cons 1 <| plist.nil) := multiset.eq_mk <| by
  simp only [plist.toList_cons, plist.toList_nil]
  exact .swap _ _ _

def ofMultiset {α} (x : Multiset α) : multiset (fun _ => α) :=
  x.lift (multiset.mk _ ∘ plist.ofList) fun a b h => multiset.eq_mk <| by
    simp only [plist.ofList_toList]
    exact h

def length : NatTrans multiset (const _ Nat) :=
  coeq.lift
    plist.length
    rfl

-- We need to find operations that are invariant under mapping,
-- these can then maybe be used to try to extract information.

-- Subsets are invariant under mapping,
-- this can be very useful.

/- def subset : NatTrans (prod) -/

/- noncomputable def toMultiset {α} (x : multiset (fun _ => α)) : Multiset α := by -/
/-   if h : ∃ v, multiset.mk _ v = x then -/
/-     sorry -/
/-   else -/
/-     simp at h -/
/-     sorry -/

theorem ofMultiset.surjective {α} [Nonempty α]
    : Function.Surjective (ofMultiset (α := α)) := by
  intro x
  have := mk_sur (by
    rintro h (_|_|_) x y rfl
    rfl
  ) (by
    rintro h (_|_|_) x y h'
    dsimp [permlist.transp,NatTrans.child] at h'
    dsimp [plist] at x y
    sorry
    ) x
  stop
  
  rintro ⟨⟨mh⟩, mc⟩
  dsimp [plist] at mh
  /- dsimp [multiset, coeq] at mc -/
  /- unfold r at mc -/
  /- dsimp [permlist.transp, permlist.proj, NatTrans.hd] at mc -/
  specialize mc .fz
  dsimp [multiset, coeq] at mc
  unfold r at mc
  dsimp [permlist.transp, permlist.proj, NatTrans.hd, NatTrans.child] at mc
  use Quot.mk _ <| List.ofFn (n := mh) sorry
  dsimp only [ofMultiset, Function.comp_apply]
  dsimp [multiset.mk, mk]
  sorry

-- NOT ACTUALLY PROVEN
theorem ofMultiset.injective {α}
    : Function.Injective (ofMultiset (α := α)) := by
  intro a b x
  cases a using Quotient.ind; next a =>
  cases b using Quotient.ind; next b =>
  dsimp [-Multiset.quot_mk_to_coe, ofMultiset] at x
  apply Quot.sound
  change a.Perm b
  have := multiset.mk_eq x
  simp only [plist.ofList_toList] at this
  exact this

example {α} : multiset (fun _ => α) ≃ Multiset α where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end

end coeq -----------------------------------------------------------------------

structure NatRel (P : MvPFunctor n) where
  r : ∀ α, P α → P α → Prop
  /-- Closed under coarsenings. Imagine it as relations that look like this:
    ⊤⊤⊤    Most complex polynomials
    / \      |
   /   \     |
  / *   \    | Complexity
  \/#\  /    |
   \##\/     |
    \#/     \|/
     ⊥     Simplet polynomial ⟨hd, λ _ ↦ Unit⟩

  This corresponds also to the notion of being an ideal. -/
  nat α β (x y : P α) (m : α ⟹ β) : r α x y → r β (m <$$> x) (m <$$> y)

/-
  P m
  a -> 1
  b -> 2
  c -> 2
  Q
  a -> 1
  b -> 2
  b -> 2

-/

namespace NatRel

variable {P Q R : MvPFunctor n}

instance : CoeFun (NatRel P) (fun _ => ∀ {α}, P α → P α → Prop) where coe := r

@[ext 900]
theorem ext {a b : NatRel P}
    (h : a.r = b.r)
    : a = b := by
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  subst h
  rfl

theorem ext' {a b : NatRel P}
    /- (h : ∀ hd hd2, a.r _ ⟨hd, TypeVec.id⟩ = b.r _ ⟨hd, TypeVec.id⟩) -/
    : a = b := by
  ext α ⟨hd, tl⟩
  sorry
  /- change a.f _ (tl <$$> ⟨hd, TypeVec.id⟩) = b.f _ (tl <$$> ⟨hd, TypeVec.id⟩) -/
  /- rw [←a.nat, ←b.nat, h] -/

/- def id (P : MvPFunctor n) : NatTrans P P := ⟨fun _ x => x, fun _ _ _ _ => rfl⟩ -/
/- def comp (u : NatTrans P Q) (v : NatTrans Q R) : NatTrans P R where -/
/-   f α x := v.f _ (u.f _ x) -/
/-   nat α β m x := calc -/
/-     m <$$> v.f α (u.f α x) -/
/-       = v.f β (m <$$> (u.f _ x)) := by rw [v.nat] -/
/-     _ = v.f β (u.f β (m <$$> x)) := by rw [u.nat] -/
/-  -/
def hd (nt : NatRel P) (a b : P.A) : Prop :=
  nt.r (fun _ => PUnit) ⟨a, fun _ _ => .unit⟩ ⟨b, fun _ _ => .unit⟩

/-  -/
/- @[simp] -/
/- theorem comp_hd -/
/-     {u : NatTrans P Q} {v : NatTrans Q R} -/
/-     : (u.comp v).hd = (v.hd ∘ u.hd) := rfl -/
/-  -/
/- theorem nt_fst_eq (nt : NatTrans P Q) {α β} -/
/-     {x : P α} {y : P β} (h : x.fst = y.fst) -/
/-     : (nt.f _ x).fst = (nt.f _ y).fst := by -/
/-   rcases x with ⟨x,x₁⟩ -/
/-   rcases y with ⟨_,y₁⟩ -/
/-   subst h -/
/-   rw [←MvPFunctor.map_fst (α := α) (arr := fun _ _ => PUnit.unit), nt.nat] -/
/-   rw [←MvPFunctor.map_fst (α := β) (arr := fun _ _ => PUnit.unit), nt.nat] -/
/-   rfl -/
/-  -/
/- @[simp] -/
/- theorem nt_fst_eq_hd (nt : NatTrans P Q) -/
/-     {α x} -/
/-     : (nt.f α x).fst = nt.hd x.1 := -/
/-   nt_fst_eq nt rfl -/
/-  -/
/- def child (nt : NatTrans P Q) (b : P.A) : Q.B (hd nt b) ⟹ P.B b := by -/
/-   refine fun i v => (nt.f (P.B b) ⟨b, TypeVec.id⟩).snd i (cast (?_) v) -/
/-   congr 2 -/
/-   refine nt_fst_eq nt rfl -/
/-  -/
/- theorem child_eq -/
/-     {f g : NatTrans P Q} -/
/-     {b : P.A} {i} -/
/-     {x y} -/
/-     {α} (tl : P.B b ⟹ α) -/
/-     (h : f.child b i x = g.child b i y) -/
/-     : (f.f α ⟨b, tl⟩).snd i (cast (by simp) x) -/
/-     = (g.f α ⟨b, tl⟩).snd i (cast (by simp) y) := by -/
/-   simp [child] at h -/
/-   change (f.f α (tl <$$> ⟨b, TypeVec.id⟩)).snd i _ = (g.f α (tl <$$> ⟨b, TypeVec.id⟩)).snd i _ -/
/-   rw! (castMode := .all) [←f.nat _ _ tl ⟨b, TypeVec.id⟩, ←g.nat _ _ tl ⟨b, TypeVec.id⟩] -/
/-   simp [eqRec_eq_cast, h] -/
/-  -/
/- theorem rev -/
/-     {v : NatTrans Q R} -/
/-     {α x i u} -/
/-     : (v.f α x).snd i u -/
/-     = x.snd i (v.child x.1 i (cast (by congr 1; simp) u)) := by -/
/-   rcases x with ⟨hd, tl⟩ -/
/-   change (v.f α (tl <$$> ⟨hd, TypeVec.id⟩)).snd i u = _ -/
/-   rw! (castMode := .all) [←v.nat] -/
/-   simp [map_mk, TypeVec.comp_id, eqRec_eq_cast, map_fst, map_snd, TypeVec.comp.get, -/
/-     Function.comp_apply, child] -/
/-  -/
/- theorem comp_child -/
/-     {u : NatTrans P Q} {v : NatTrans Q R} {i b x} -/
/-     : u.child b i (v.child (u.hd b) i x) = (u.comp v).child b i x := by -/
/-   symm -/
/-   unfold comp child -/
/-   dsimp -/
/-   rw [rev] -/
/-   simp only [cast_cast] -/
/-   congr! -/
/-   change v.child _ _ _ = _ -/
/-   rw! [u.nt_fst_eq_hd] -/
/-   rfl -/
/-  -/
/- theorem nt_snd_eq_child -/
/-     {v : NatTrans Q R} -/
/-     {α x} -/
/-     : (v.f α x).snd -/
/-     = x.snd ⊚ (v.child x.1) ⊚ (.mp <| by simp) := by -/
/-   funext i h -/
/-   simp [rev] -/
/-  -/
/- theorem transform_mk -/
/-     {v : NatTrans Q R} -/
/-     {α hd tl} -/
/-     : v.f α ⟨hd, tl⟩ = ⟨v.hd hd, tl ⊚ v.child hd⟩ := by -/
/-   change v.f α (tl <$$> ⟨hd, TypeVec.id⟩) = tl <$$> ⟨v.hd hd, v.child hd⟩ -/
/-   rw [←v.nat] -/
/-   congr -/
/-   apply Sigma.ext -/
/-   · simp -/
/-   · simp only [nt_snd_eq_child, TypeVec.id_comp] -/
/-     rw [TypeVec.heq_of_mp_mpr rfl (by simp)] -/
/-     simp -/

end NatRel

def quot {P : MvPFunctor n}
    (r : NatRel P)
    : MvPFunctor n where
  A := Quot r.hd
  B e i :=
    { c : ∀ d, Quot.mk _ d = e → P.B d i //
      ∀ b, ∀ h : Quot.mk _ b = e, ∀ α, ∀ t1 t2,
        r.r α ⟨b, t1⟩ ⟨b, t2⟩
        → True
        /- True -/
        /- f.child b i (c (f.hd b) h) = -/
        /- g.child b i (c (g.hd b) <| by -/
        /-   subst h -/
        /-   apply Quot.sound ⟨_, rfl, rfl⟩ -/
        /- ) -/
    }

namespace quot

variable {P : MvPFunctor n} (r : NatRel P) {α}

def mk {α} (x : P α) : quot r α where
  fst := Quot.mk _ x.1
  snd i v := x.2 i (v.1 x.fst rfl)

#check Quot.hrecOn

def lift {α O} (f : P α → O) (sound : ∀ a b, r.r _ a b → f a = f b)
      (v : quot r α) : O := by
  have ⟨f, s⟩ := v
  induction f using Quot.hrecOn
  case f f =>
    have : P α := ⟨f, fun i x => by
      apply s
      dsimp [quot]
      refine ⟨?_, ?_⟩
      · intro b h
        sorry
      · sorry
      ⟩
    sorry
  · sorry

end quot

end MvPFunctor


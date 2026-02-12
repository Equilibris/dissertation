import CoinductivePredicates
import Sme.ITree.Defs
import Sme.ITree.Combinators
import Sme.ITree.KTree
import Sme.ITree.WBisim.Step

namespace Sme

universe u v

variable {E : Type u → Type u} {A B : Type _} {a b c : ITree E A}

namespace ITree

coinductive WBisim' (E : Type u → Type u) (A : Type v)
    : Base E (ITree E A) A → Base E (ITree E A) A → Prop where
  -- This case only exists for refl spin spin,
  -- in fact it could be this,
  -- but that would be harder to prove things about
  | refl {a b c} : EStep a c → EStep b c → WBisim' E A a b
  | ret {a b v}
      : Step a (.ret v) → Step b (.ret v) → WBisim' E A a b
  | vis {V e a b a' b'}
      : Step a (.vis e a') → Step b (.vis e b') →
        (∀ v : V, WBisim' (a' v).dest (b' v).dest) → WBisim' E A a b

namespace WBisim'

namespace Invariant

@[simp]
theorem refl'
    {R a}
    : WBisim'.Invariant E A R a a := 
  .refl (.refl _) (.refl _)

@[simp]
theorem symm
    {R a b}
    : WBisim'.Invariant E A R a b → WBisim'.Invariant E A (flip R) b a
  | .refl ha hb => .refl hb ha
  | .ret ha hb => .ret hb ha
  | .vis ha hb h => .vis hb ha h

theorem eqSpin {R b}
    (v : Invariant E A R (Base.tau spin) b)
    : Base.tau spin = b := by
  rcases v with (⟨h, h'⟩|h|h)
  · obtain rfl := h.eqSpin
    obtain rfl := h'.spinEq
    rfl
  · exact h.not_spin'.elim
  · exact h.not_spin'.elim

@[simp]
theorem eqSpin_iff {R b}
    : Invariant E A R (Base.tau spin) b
    ↔ Base.tau spin = b where
  mp := eqSpin
  mpr h := h ▸ .refl'

@[simp]
theorem spinEq_iff {R b}
    : Invariant E A R b (Base.tau spin)
    ↔ Base.tau spin = b where
  mp h := eqSpin h.symm
  mpr h := h ▸ .refl'

theorem ofEstep {R c d}
    (v' : EStep d c)
    : Invariant E A R c d := by
  refine .refl (.refl _) v'

theorem antisymm {R}
    {a b : Base E _ A}
    (hab : EStep a b) (hba : EStep b a)
    : Invariant E A R a b := by
  rcases Step.no_middle a with (rfl|⟨_,⟨h⟩⟩|⟨_,_,_,⟨h⟩⟩)
  · obtain rfl := hab.eqSpin
    exact .refl (.refl _) (.refl _)
  · exact .ret h (EStep.step_comp hba h)
  · refine .refl h.toEStep (EStep.step_comp hba h).toEStep

-- TODO: Clean...
theorem skip
    {R : _ → _ → Prop} {a b c d}
    (ha : EStep a c) (ha : EStep b d)
    (v : WBisim'.Invariant E A R c d)
    : WBisim'.Invariant E A R a b := by
  rcases Step.no_middle c with (rfl|⟨_,⟨r⟩⟩|⟨_,_,_,⟨r⟩⟩)
  · obtain rfl:= ha.spinEq
    obtain rfl := v.eqSpin
    obtain rfl:= ha.spinEq
    exact .refl (.refl _) (.refl _)
  · rename_i ha' _
    rcases v with (⟨v', v⟩|⟨v', v⟩|⟨v', v, h⟩)
    · exact .refl (ha'.trans v') (ha.trans v)
    · refine .ret (ha'.step_comp v') (ha.step_comp v)
    · refine .vis (ha'.step_comp v') (ha.step_comp v) h
  · rename_i ha' _ _ _
    rcases v with (⟨v', v⟩|⟨v', v⟩|⟨v', v, h⟩)
    · exact .refl (ha'.trans v') (ha.trans v)
    · refine .ret (ha'.step_comp v') (ha.step_comp v)
    · refine .vis (ha'.step_comp v') (ha.step_comp v) h

theorem shrink
    {R : _ → _ → Prop} {a b c d}
    (ha : EStep a c) (hb : EStep b d)
    (v : WBisim'.Invariant E A R a b)
    : WBisim'.Invariant E A R c d := by
  rcases v with (⟨x, y⟩|⟨x, y⟩|⟨x,y,h⟩)
  · exact refl
      (c := (x.maxl ha).max (y.maxl hb))
      ((x.maxr ha).trans (EStep.maxl _ _))
      ((y.maxr hb).trans (EStep.maxr _ _))
  · have ha := ha.maxl x.toEStep
    have hb := hb.maxl y.toEStep
    simp at ha hb
    exact .ret ha.toRetStep' hb.toRetStep'
  · have ha := ha.maxl x.toEStep
    have hb := hb.maxl y.toEStep
    simp at ha hb
    exact .vis ha.toVisStep' hb.toVisStep' h

end Invariant

theorem unfold : Is E A (WBisim' E A) :=
  fun ⟨r, ris, rab⟩ =>
    match ris rab with
    | .refl ha hb => .refl ha hb
    | .ret a b => .ret a b
    | .vis a b h => .vis a b fun v => ⟨r, ris, h v⟩

@[refl]
theorem refl {a} : WBisim' E A a a := ⟨(· = ·), fun v => v ▸ .refl (.refl _) (.refl _), rfl⟩

theorem ret {a b v} (ha : Step a (.ret v)) (hb : Step b (.ret v))
    : WBisim' E A a b := ⟨
  (Nonempty <| Step · (.ret v) × Step · (.ret v)),
  fun ⟨a, b⟩ => .ret a b,
  ⟨ha, hb⟩
⟩

theorem vis {V e a b a' b'}
      (ha : Step a (.vis e a')) (hb : Step b (.vis e b'))
      (h : ∀ v : V, WBisim' E A (a' v).dest (b' v).dest)
      : WBisim' E A a b := ⟨
  (fun a b => WBisim' E A a b ∨ Nonempty (Step a (.vis e a') × Step b (.vis e b'))),
  fun
    | .inl v =>
      match v.unfold with
      | .refl ha hb => .refl ha hb
      | .ret a b => .ret a b
      | .vis a b h => .vis a b fun _ => .inl <| h _
    | .inr ⟨a, b⟩ => .vis a b fun _ => .inl <| h _,
  .inr ⟨ha, hb⟩
⟩

theorem eqSpin {a} (h : WBisim' E A a spin.dest) : a = spin.dest :=
  match h.unfold with
  | .refl ha hb => by
    obtain rfl := (spin.dest_eq ▸ hb).eqSpin
    obtain rfl := ha.spinEq
    rw [spin.dest_eq]
  | .ret _ v => (Step.not_spin v).elim
  | .vis _ v _ => (Step.not_spin v).elim

theorem eqSpin' {a} (h : WBisim' E A a (.tau spin)) : a = (.tau spin) := by
  rw [←spin.dest_eq] at h ⊢
  exact eqSpin h

theorem symm {a b} : WBisim' E A a b → WBisim' E A b a :=
  fun ⟨r, ris, rab⟩ => ⟨
    fun a b => r b a,
    fun rab =>
      match ris rab with
      | .ret a b => .ret b a
      | .refl ha hb => .refl hb ha
      | .vis a b h => .vis b a h,
    rab,
  ⟩

@[elab_as_elim]
theorem cases {a b} {motive : Base E _ A → Base E _ A → Prop}
    (h : WBisim' E A a b)
    (hRefl : motive (.tau spin) (.tau spin))
    (hRet : {v : _} → Step a (.ret v) → Step b (.ret v) → motive a b)
    (hVis : {V e f g : _}
      → Step a (.vis e f)
      → Step b (.vis e g)
      → (∀ v : V, WBisim' E A (f v).dest (g v).dest) → motive a b)
    : motive a b :=
  match h.unfold with
  | .refl ha hb => by
    /- have :=  -/
    rcases Step.no_middle a with (rfl|⟨_, ⟨p⟩⟩|⟨_,_,f,⟨p⟩⟩)
    · obtain rfl:= h.symm.eqSpin'
      exact hRefl
    · apply hRet p (EStep.triag ha hb p)
    · apply hVis p (EStep.triag ha hb p) fun _ => .refl
  | .ret a b => hRet a b
  | .vis a b h => hVis a b h

theorem trans {a b c} : WBisim' E A a b → WBisim' E A b c → WBisim' E A a c :=
  fun ⟨r, ris, rab⟩ ⟨r', ris', rbc⟩ => ⟨
    (fun a c => r a c ∨ r' a c ∨ ∃ b, r a b ∧ r' b c),
    fun
      | .inl v  => (match ris v with
        | .refl ha hb => .refl ha hb
        | .ret a b => .ret a b
        | .vis a b h => .vis a b fun v => .inl (h v))
      | .inr <| .inl v  => (match ris' v with
        | .refl ha hb => .refl ha hb
        | .ret a b => .ret a b
        | .vis a b h => .vis a b fun v => .inr <| .inl (h v))
      | .inr <| .inr ⟨_, rab, rbc⟩ => (match ris rab, ris' rbc with
        | .refl ha hb, .refl ha' hb' =>
          .skip ha hb' (.shrink hb ha' .refl')
        | .ret a b, .refl ha hb =>
          .skip (.refl _) hb <| .shrink (.refl _) ha <| .ret a b
        | .refl ha hb, .ret a b =>
          .skip ha (.refl _) <| .shrink hb (.refl _) <| .ret a b
        | .vis a b h, .refl ha hb =>
          .skip (.refl _) hb <| .shrink (.refl _) ha <| .vis a b (fun x => .inl <| h x)
        | .refl ha hb, .vis a b h =>
          .skip ha (.refl _) <| .shrink hb (.refl _) <| .vis a b (fun x => .inr <| .inl <| h x)
        | .vis a b h, .vis b' a' h' => by
          obtain ⟨rfl, rfl, rfl⟩ := (Base.vis.injEq _ _ _ _ _).mp <| b.eq b'
          exact .vis a a' (fun v => .inr <| .inr <| ⟨_, h v, h' v⟩)
        | .ret a b, .ret b' a' => by
          obtain ⟨rfl, rfl, rfl⟩ := (Base.ret.injEq _ _).mp <| b.eq b'
          exact .ret a a'
        | .ret _ h, .vis h' _ _
        | .vis _ h' _, .ret h _ => by
          have := Step.eq h h'
          contradiction),
    .inr <| .inr ⟨_, rab, rbc⟩,
  ⟩

theorem tau {a} : WBisim' E A (Base.tau a) a.dest := ⟨
  (fun a b => Nonempty (EStep a b)),
  fun {a b} ⟨ha⟩ => by
    rcases Step.no_middle b with (rfl|⟨_, ⟨h⟩⟩|⟨_,_,_, ⟨h⟩⟩)
    · obtain rfl := ha.spinEq
      exact .refl (.refl _) (.refl _)
    · refine .ret ?_ h
      exact ha.step_comp h
    · refine .vis (ha.step_comp h) h fun _ => ⟨.refl _⟩
  ,
  ⟨.tau <| .refl _⟩
⟩

theorem ofEStep {a b} : EStep a b → WBisim' E A a b
  | .tau h => .trans tau (ofEStep h)
  | .refl _ => .refl

end WBisim'

def WBisim {E : Type u → Type u} {A : Type v} (a b : ITree E A) : Prop :=
  WBisim' E A a.dest b.dest

end ITree

instance : HasEquiv (ITree E A) := ⟨ITree.WBisim⟩

namespace ITree

namespace WBisim

@[refl] theorem refl :   a ≈ a := WBisim'.refl
@[symm] theorem symm :   a ≈ b → b ≈ a := WBisim'.symm
@[trans] theorem trans : a ≈ b → b ≈ c → a ≈ c := WBisim'.trans

instance : Equivalence (· ≈ · : ITree E A → _ → _) where
  refl _ := refl
  symm := symm
  trans := trans

theorem eqSpin (h : a ≈ spin) : a = spin :=
  dest.inj_eq.mp <| WBisim'.eqSpin h


@[simp]
theorem spinEq_iff : spin ≈ a ↔ a = spin where
  mp h := eqSpin h.symm
  mpr h := h ▸ .refl

@[simp]
theorem eqSpin_iff : a ≈ spin ↔ a = spin where
  mp := eqSpin
  mpr h := h ▸ .refl

inductive WBisimAlt : ITree E A → ITree E A → Prop
  | spin : WBisimAlt spin spin
  | ret {v a b} : Step a.dest (.ret v) → Step b.dest (.ret v) → WBisimAlt a b
  | vis {e a' b' a b} :
      (∀ v, WBisim (a' v) (b' v))
      → Step a.dest (.vis e a') → Step b.dest (.vis e b')
      → WBisimAlt a b

theorem unfold' {a b : ITree E A} (h : WBisim a b) : WBisimAlt a b := by
  cases h.unfold
  case refl c ha hb => 
    rcases Step.no_middle c with (rfl|⟨_, ⟨h⟩⟩|⟨_,_,_,⟨h⟩⟩)
    · have ha := ha.spinEq
      have hb := hb.spinEq
      rw [←spin.dest_eq] at ha hb
      cases ITree.dest_eq_iff.mpr ha
      cases ITree.dest_eq_iff.mpr hb
      exact .spin
    · refine .ret (ha.step_comp h) (hb.step_comp h)
    · refine .vis (fun _ => .refl) (ha.step_comp h) (hb.step_comp h)
  case ret ha hb => exact .ret ha hb
  case vis h ha hb => exact .vis h ha hb

/- @[elab_as_elim] -/
/- theorem cases {a b} {motive : ITree E A → ITree E A → Prop} -/
/-     (h : WBisim a b) -/
/-     (taul : ∀ a b, motive a b → motive (.tau a) b) -/
/-     (taur : ∀ a b, motive a b → motive a (.tau b)) -/
/-     (hRefl : motive (.tau spin) (.tau spin)) -/
/-     (hRet : {v : _} → Step a.dest (.ret v) → Step b.dest (.ret v) → motive (.ret v) (.ret v)) -/
/-     (hVis : {V e f g : _} -/
/-       → Step a.dest (.vis e f) -/
/-       → Step b.dest (.vis e g) -/
/-       → (∀ v : V, WBisim (f v) (g v)) → motive (.vis e f) (.vis e g)) -/
/-     : motive a b := by -/
/-   have := h.unfold -/
/-   cases this -/
/-   · sorry -/
/-   · sorry -/
/-   · sorry -/

theorem tau : .tau a ≈ a := by
  change WBisim' _ _ _ _
  rw [dest_tau]
  exact WBisim'.tau

@[simp]
theorem tau_bind {f : _ → ITree E B} {a : ITree E A} : bind (.tau a) f ≈ bind a f :=
  ITree.tau_bind ▸ tau

theorem ret {v} (ha : Step a.dest (.ret v)) (hb : Step b.dest (.ret v))
    : a ≈ b := WBisim'.ret ha hb

theorem vis {V e a' b'}
      (ha : Step a.dest (.vis e a')) (hb : Step b.dest (.vis e b'))
      (h : ∀ v : V, (a' v) ≈ (b' v))
      : a ≈ b := WBisim'.vis ha hb h

instance : Trans (· ≈ · : ITree E A → _ → Prop) (· ≈ ·) (· ≈ ·) where
  trans := trans

instance : Trans (WBisim (E := E) (A := A)) WBisim WBisim := ⟨WBisim.trans⟩
instance : Trans (WBisim (E := E) (A := A)) Eq WBisim where
  trans a b := b ▸ a
instance : Trans Eq (WBisim (E := E) (A := A)) WBisim where
  trans a b := a ▸ b


end ITree.WBisim

namespace KTree

open scoped ITree

def WBisim {A B} : KTree E A B → KTree E A B → Prop :=
  fun a b => ∀ v, a v ≈ b v

instance : HasEquiv (A → ITree E A) := ⟨WBisim⟩
instance : HasEquiv (KTree E A B) := ⟨WBisim⟩

end KTree

scoped infix:100 " ≈ₖ " => KTree.WBisim

namespace ITree.WBisim'
def stepRet {a b c} : Step a (.ret c) → WBisim' E A a b → Nonempty (Step b (.ret c)) :=
  fun he hb =>
  have := hb.symm.trans <| ofEStep he.toEStep
  by
  rcases this.unfold with (⟨ha, hb⟩|⟨h',(_|_)⟩|⟨_,(_|_),_⟩)
  · obtain rfl := hb.ret
    exact ha.toRetStep
  · exact ⟨h'⟩

theorem stepVis {X} {a b e k}
    : Step a (.vis (e : E X) k) → WBisim' E A a b → ∃ k', k' ≈ₖ k ∧ Nonempty (Step b (.vis e k')) :=
  fun he hb =>
  have := hb.symm.trans <| ofEStep he.toEStep
  by
  rcases this.unfold with (⟨ha, hb⟩|⟨h',(_|_)⟩|⟨_,(_|_),_⟩)
  · obtain rfl := hb.vis
    exact ⟨_, fun _ => .refl, ha.toVisStep⟩
  · rename_i h a
    exact ⟨_, a, ⟨h⟩⟩

end ITree.WBisim'

namespace ITree.WBisim

theorem stepRet {c} : Step a.dest (.ret c) → a ≈ b → Nonempty (Step b.dest (.ret c)) :=
  (WBisim'.stepRet · ·)

theorem stepVis {X} {e k}
    : Step a.dest (.vis (e : E X) k) → a ≈ b 
    → ∃ k', k' ≈ₖ k ∧ Nonempty (Step b.dest (.vis e k')) :=
  (WBisim'.stepVis · ·)

end Sme.ITree.WBisim

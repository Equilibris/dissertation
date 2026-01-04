import CoinductivePredicates
import Sme.ITree.Defs
import Sme.ITree.Combinators
import Sme.ITree.KTree

namespace Sme

universe u v

variable {E : Type u → Type u} {A B C : Type _}

namespace ITree

/-- Given Some sequence of taus, they are related to the first productive value
  Step (tau (tau (r))) r
-/
inductive Step : Base E (ITree E A) A → Base E (ITree E A) A → Type _
  | tau {a b} : Step a.dest b → Step (.tau a) b
  | ret {v} : Step (.ret v) (.ret v)
  | vis {e k} : Step (.vis e k) (.vis e k)

namespace Step

theorem eq {a b c : Base E (ITree E A) A}
    : Step a b → Step a c → b = c
  | .tau a, .tau b => eq a b
  | .ret, .ret | .vis, .vis => rfl

instance {X Y : Base E _ A} : Subsingleton (Step X Y) where
  allEq := ae
where ae {X Y} : ∀ (a b : Step X Y), a = b
  | .tau u, .tau v => ae u v ▸ rfl
  | .ret , .ret | .vis , .vis => rfl

theorem tau_rhs {V : Base E _ A} {v'} : Step V (.tau v') → False
  | .tau v => tau_rhs v

theorem not_spin {V} (v : Step (spin : ITree E A).dest V) : False := by
  generalize h : spin.dest = x at v
  rw [spin.dest_eq] at h
  induction v
  case tau ih =>
    rw [Base.tau.injEq] at h
    subst h
    simp only [spin.dest_eq, imp_false, not_true_eq_false] at ih
  · contradiction
  · contradiction

theorem not_spin' {V} : Step (.tau (spin : ITree E A)) V → False
  | .tau a => not_spin a

theorem not_step {V : ITree E A} (v : ∀ {v}, Step V.dest v → False) : V = spin :=
  bisim ⟨
    (fun a b => (∀ {x}, Step a x → False) ∧ (∀ {y}, Step b y → False)),
    fun {a b} ⟨ha, hb⟩ => match a, b with
      | .ret _,   _        => (ha .ret).elim
      | .vis _ _, _        => (ha .vis).elim
      | _,        .ret _   => (hb .ret).elim
      | _,        .vis _ _ => (hb .vis).elim
      | .tau _,   .tau _   => .tau ⟨fun h => ha (.tau h), fun h => hb (.tau h)⟩
      ,
    ⟨v, not_spin⟩,
  ⟩

theorem not_step' {V : Base E _ A} (v : ∀ {v}, Step V v → False) : V = (.tau spin) := by
  refine mk_eq ?_
  rw [←spin.dest_eq, dest_mk]
  apply not_step
  intro _ a
  rw [mk_dest] at a
  apply v a

theorem no_middle (V : Base E _ A)
    : V = .tau spin
    ∨ (∃ v, Nonempty (Step V (.ret v))) ∨
    (∃ A e f, Nonempty (Step V (.vis (e : E A) f))) := by 
  by_cases h : (∀ {v}, Step V v → False)
  · exact .inl (not_step' h)
  simp only [not_forall, not_false_eq_true, exists_const_iff, and_true] at h
  rcases h with ⟨(_|_|_), ⟨p⟩⟩
  · exact (tau_rhs p).elim
  · exact .inr <| .inl ⟨_, ⟨p⟩⟩
  · exact .inr <| .inr ⟨_,_,_, ⟨p⟩⟩

end Step

/-- EStep (tau (tau (r))) (tau r) -/
inductive EStep : Base E (ITree E A) A → Base E (ITree E A) A → Type _
  | tau {a b} : EStep a.dest b → EStep (.tau a) b
  | refl a : EStep a a

def Step.toEStep {a b : Base E _ A} : Step a b → EStep a b
  | .vis | .ret => .refl _
  | .tau h => .tau (toEStep h)

namespace EStep

def trans : {a b c : Base E (ITree E A) A}
    → EStep a b → EStep b c → EStep a c
  | _,_,_, .refl _, .refl _ => .refl _
  | _,_,_, .refl _, .tau h
  | _,_,_, .tau h , .refl _ => .tau h
  | _,_,_, .tau a, .tau b => .tau <| trans a (.tau b)

def step_comp {a b c : Base E _ A} : EStep a b → Step b c → Step a c
  | .refl _, v => v
  | .tau h, ha => .tau (step_comp h ha)

theorem spinEq {a} (h : EStep a (.tau (spin : ITree E A))) : a = .tau spin := by
  generalize h' : Base.tau (spin : ITree E A) = v at h
  induction h
  case tau h =>
    subst h'
    specialize h rfl
    rw [←spin.dest_eq] at h
    obtain rfl := dest.inj_eq.mp h
    simp
  · rfl

theorem eqSpin {a} (h : EStep (.tau (spin : ITree E A)) a) : a = .tau spin := by
  generalize h' : Base.tau (spin : ITree E A) = v at h
  induction h
  case tau ih =>
    obtain rfl := Base.tau.inj h'
    rw [spin.dest_eq] at ih
    exact ih rfl
  · rfl

def middle : {a c d : Base E _ A} → EStep a c → EStep a d → (EStep d c ⊕ EStep c d)
  | _, _, _, .refl _, h => .inr h
  | _, _, _, .tau h', .refl _ => .inl <| .tau h'
  | _, _, _, .tau h', .tau h => middle h' h

def meet {a b c : Base E _ A} : EStep a b → Step a c → Step b c
  | .tau h, .tau h' => meet h h'
  | .refl _, v => v

def triag {a b c d : Base E _ A} : EStep a c → EStep b c → Step a d → Step b d
  | .refl _, h, h' => h.step_comp h'
  | .tau ha, .tau hb, .tau h' =>
    .tau (triag ha hb h')
  | .tau ha, .refl _, .tau hb => meet ha hb

def max {a b c : Base E _ A} : EStep a b → EStep a c → Base E (ITree E A) A
  | .refl _, _ => c
  | _, .refl _ => b
  | .tau ha, .tau hb => max ha hb

theorem max_comm {a b c : Base E _ A} : (x : EStep a b) → (y : EStep a c) → max x y = max y x
  | .refl _, .refl _ | .tau _, .refl _ | .refl _, .tau _ => rfl
  | .tau x, .tau y => max_comm x y

@[simp]
theorem max_toEStep_l {a b c : Base E _ A} : {x : EStep a b} → {y : Step a c} → max x y.toEStep = c
  | .refl _, _ => by simp only [max]
  | .tau a, .tau b => by
    simp only [Step.toEStep, max]
    apply max_toEStep_l

@[simp]
theorem max_toEStep_r
    {a b c : Base E _ A} {x : EStep a b} {y : Step a c} : max y.toEStep x = c := by
  rw [max_comm, max_toEStep_l]

def maxl {a b c : Base E _ A} : (x : EStep a b) → (y : EStep a c) → EStep b (max x y)
  | .refl _, .refl _ => .refl _
  | .refl _, .tau v => .tau v
  | .tau v, .refl _ => .refl _
  | .tau ha, .tau hb => maxl ha hb

def maxr {a b c : Base E _ A} : (x : EStep a b) → (y : EStep a c) → EStep c (max x y)
  | .refl _, .refl _ => .refl _
  | .refl _, .tau v => .refl _
  | .tau v, .refl _ => .tau v
  | .tau ha, .tau hb => maxr ha hb

@[simp]
def ret {w v} : EStep (.ret w) (v : Base E _ A) → v = .ret w
  | .refl _ => rfl

@[simp]
def vis {X e k v} : EStep (.vis (e : E X) k) (v : Base E _ A) → v = .vis e k
  | .refl _ => rfl

theorem toRetStep {v} {a : Base E _ A}
    (h : EStep a (.ret v)) : Nonempty (Step a (.ret v)) := by 
  rcases Step.no_middle a with (rfl|⟨w,⟨p⟩⟩|⟨_,_,_,⟨p⟩⟩)
  · have := EStep.eqSpin h
    contradiction
  · cases meet h p
    exact ⟨p⟩
  · cases meet h p

theorem toVisStep {X e k} {a : Base E _ A}
    (h : EStep a (.vis (e : E X) k)) : Nonempty (Step a (.vis e k)) := by 
  rcases Step.no_middle a with (rfl|⟨w,⟨p⟩⟩|⟨_,_,_,⟨p⟩⟩)
  · have := EStep.eqSpin h
    contradiction
  · cases meet h p
  · cases meet h p
    exact ⟨p⟩

def transp_bind_map
    (f : A → ITree E B) {a b : Base E _ A}
    : EStep a b
    → EStep (bind_map f a) (bind_map f b)
  | .tau h => .tau <| dest_bind ▸ transp_bind_map f h
  | .refl _ => .refl _

end EStep

coinductive WBisim' (E : Type u → Type u) (A : Type (u + 1))
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

theorem eqSpin {R b}
    (v : Invariant E A R (Base.tau spin) b)
    : Base.tau spin = b := by
  rcases v with (⟨h, h'⟩|h|h)
  · obtain rfl := h.eqSpin
    obtain rfl := h'.spinEq
    rfl
  · exact h.not_spin'.elim
  · exact h.not_spin'.elim

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

theorem refl'
    {R a}
    : WBisim'.Invariant E A R a a := 
  .refl (.refl _) (.refl _)

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
    exact .ret (Classical.choice ha.toRetStep) (Classical.choice hb.toRetStep)
  · have ha := ha.maxl x.toEStep
    have hb := hb.maxl y.toEStep
    simp at ha hb
    exact .vis (Classical.choice ha.toVisStep) (Classical.choice hb.toVisStep) h

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

def WBisim {E : Type u → Type u} {A : Type (u + 1)} (a b : ITree E A) : Prop :=
  WBisim' E A a.dest b.dest

end ITree

infix:100 " ≈ " => ITree.WBisim

namespace ITree

namespace WBisim

variable {a b c : ITree E A}

@[refl] theorem refl :   a ≈ a := WBisim'.refl
@[symm] theorem symm :   a ≈ b → b ≈ a := WBisim'.symm
@[trans] theorem trans : a ≈ b → b ≈ c → a ≈ c := WBisim'.trans

instance : Equivalence (· ≈ · : ITree E A → _ → _) where
  refl _ := refl
  symm := symm
  trans := trans

theorem eqSpin (h : a ≈ spin) : a = spin :=
  dest.inj_eq.mp <| WBisim'.eqSpin h

-- TODO:
@[elab_as_elim]
theorem cases {motive : ITree E A → ITree E A → Prop}
    (h : WBisim a b)
    (hRefl : motive (.tau spin) (.tau spin))
    (hRet : {v : _} → Step a.dest (.ret v) → Step b.dest (.ret v) → motive a b)
    (hVis : {V e f g : _}
      → Step a.dest (.vis e f)
      → Step b.dest (.vis e g)
      → (∀ v : V, WBisim (f v) (g v)) → motive a b)
    : motive a b := by
  sorry

theorem tau : .tau a ≈ a := by
  rw [WBisim, dest_tau]
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

end ITree.WBisim

namespace KTree

open scoped ITree

def WBisim {A B} : KTree E A B → KTree E A B → Prop :=
  fun a b => ∀ v, a v ≈ b v

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

variable {A B : Type (u + 1)} {X : Type u}

variable {a b : ITree E A}

theorem tau_congr
    (h : a ≈ b)
    : ITree.tau a ≈ ITree.tau b := calc
  a.tau
    ≈ a     := tau
  _ ≈ b     := h
  _ ≈ b.tau := tau.symm

theorem vis_congr {e : E X} {k1 k2 : KTree E X A} (h : k1 ≈ₖ k2)
    : ITree.vis e k1 ≈ .vis e k2 :=
  vis (e := e) (dest_vis ▸ Step.vis) (dest_vis ▸ Step.vis) h

theorem bind_congr_arg
    {X} {k1 : KTree E A X}
    (h : a ≈ b)
    : bind a k1 ≈ bind b k1 := by
  simp only [WBisim, dest_bind]
  refine ⟨
    fun a b => ∃ c d , WBisim' E A c d
        ∧ bind_map k1 c = a
        ∧ bind_map k1 d = b,
    ?_,
    ⟨_,_, h, rfl, rfl⟩
  ⟩
  rintro a b (⟨x, y, h, rfl, rfl⟩)
  rcases Step.no_middle y with (rfl|⟨⟨_,⟨h'⟩⟩⟩|⟨⟨_,_,_,⟨h'⟩⟩⟩)
  · obtain rfl := h.eqSpin'
    exact .refl (.refl _) (.refl _)
  · have ⟨h⟩ := WBisim'.stepRet h' h.symm
    have h := h.toEStep.transp_bind_map k1
    have h' := h'.toEStep.transp_bind_map k1
    simp only [bind_map.ret] at h h'
    exact .refl h h'
  · have ⟨_, bs, ⟨h⟩⟩ := WBisim'.stepVis h' h.symm
    have h := h.toEStep.transp_bind_map k1
    have h' := h'.toEStep.transp_bind_map k1
    refine .vis (Classical.choice h.toVisStep) (Classical.choice h'.toVisStep) ?_
    intro v
    simp only [Function.comp_apply, dest_bind]
    refine ⟨_, _, bs v, rfl, rfl⟩

theorem bind_congr_cont
    {X} {k1 k2 : KTree E A X}
    (h : k1 ≈ₖ k2)
    : bind a k1 ≈ bind a k2 := by
  simp only [WBisim, dest_bind]
  refine ⟨
    fun a b => WBisim' E X a b ∨ ∃ k1 k2 v, k1 ≈ₖ k2
        ∧ bind_map k1 v = a
        ∧ bind_map k2 v = b,
    ?_,
    .inr ⟨_,_, _, h, rfl, rfl⟩
  ⟩
  rintro a b (h|⟨k1, k2, w, h, rfl, rfl⟩)
  · exact match h.unfold with
    | .refl ha hb => .refl ha hb
    | .ret ha hb => .ret ha hb
    | .vis ha hb h => .vis ha hb (.inl <| h ·)
  rcases Step.no_middle w with (rfl|⟨⟨w,⟨h'⟩⟩⟩|⟨⟨_,_,_,⟨h'⟩⟩⟩)
  · simp only [bind_map.tau, spin.bind_eq]
    exact .refl'
  all_goals
    apply WBisim'.Invariant.skip
      (h'.toEStep.transp_bind_map k1)
      (h'.toEStep.transp_bind_map k2)
  all_goals dsimp
  · specialize h w
    exact match h.unfold with
    | .refl ha hb => .refl ha hb
    | .ret ha hb => .ret ha hb
    | .vis ha hb h => .vis ha hb (.inl <| h ·)
  · refine .vis .vis .vis fun w => .inr ?_
    simp only [Function.comp_apply, dest_bind]
    exact ⟨_,_,_, h, rfl, rfl⟩

theorem bind_congr {X} {k1 k2 : KTree E A X}
    (h : a ≈ b)
    (h' : k1 ≈ₖ k2)
    : bind a k1 ≈ bind b k2 := calc
  bind a k1
    ≈ bind a k2 := bind_congr_cont h'
  _ ≈ bind b k2 := bind_congr_arg h

theorem iter_bisim {it : A → ITree E (A ⊕ B)} {v}
    : iter it v ≈ (it v).bind (Sum.elim (iter it) ITree.ret) := by
  rw [iter_eq]
  exact bind_congr_cont fun | .inr _ => .refl | .inl _ => tau

end ITree.WBisim

end Sme


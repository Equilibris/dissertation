import CoinductivePredicates
import Sme.ITree.Defs
import Sme.ITree.Combinators

namespace Sme.ITree

universe u v

variable {E : Type u → Type u} {A B C : Type (u + 1)}

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

inductive EStep : Base E (ITree E A) A → Base E (ITree E A) A → Type _
  | tau {a b} : EStep a.dest b → EStep (.tau a) b
  | refl a : EStep a a

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

theorem spin {a} (h : EStep a ((spin : ITree E A).dest)) : a = spin.dest := by
  generalize h' : ITree.dest ITree.spin = v at h
  induction h
  case tau h =>
    subst h'
    specialize h rfl
    obtain rfl := dest.inj_eq.mp h
    simp
  · rfl

end EStep

coinductive WBisim' (E : Type u → Type u) (A : Type (u + 1))
    : Base E (ITree E A) A → Base E (ITree E A) A → Prop where
  -- This case only exists for refl spin spin,
  -- in fact it could be this,
  -- but that would be harder to prove things about
  | refl {a} : WBisim' E A a a
  | ret {a b v}
      : Step a (.ret v) → Step b (.ret v) → WBisim' E A a b
  | vis {V e a b a' b'}
      : Step a (.vis e a') → Step b (.vis e b') →
        (∀ v : V, WBisim' (a' v).dest (b' v).dest) → WBisim' E A a b

namespace WBisim'

theorem unfold : Is E A (WBisim' E A) :=
  fun ⟨r, ris, rab⟩ =>
    match ris rab with
    | .refl => .refl
    | .ret a b => .ret a b
    | .vis a b h => .vis a b fun v => ⟨r, ris, h v⟩

@[refl]
theorem refl {a} : WBisim' E A a a := ⟨(· = ·), fun v => v ▸ .refl, rfl⟩

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
      | .refl => .refl
      | .ret a b => .ret a b
      | .vis a b h => .vis a b fun _ => .inl <| h _
    | .inr ⟨a, b⟩ => .vis a b fun _ => .inl <| h _,
  .inr ⟨ha, hb⟩
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
  | .refl => by
    rcases Step.no_middle a with (rfl|⟨_, ⟨p⟩⟩|⟨_,_,f,⟨p⟩⟩)
    · exact hRefl
    · exact hRet p p
    · apply hVis p p fun _ => .refl
  | .ret a b => hRet a b
  | .vis a b h => hVis a b h

theorem symm {a b} : WBisim' E A a b → WBisim' E A b a :=
  fun ⟨r, ris, rab⟩ => ⟨
    fun a b => r b a,
    fun rab =>
      match ris rab with
      | .ret a b => .ret b a
      | .refl => .refl
      | .vis a b h => .vis b a h,
    rab,
  ⟩

theorem trans {a b c} : WBisim' E A a b → WBisim' E A b c → WBisim' E A a c :=
  fun ⟨r, ris, rab⟩ ⟨r', ris', rbc⟩ => ⟨
    (fun a c => r a c ∨ r' a c ∨ ∃ b, r a b ∧ r' b c),
    fun
      | .inl v  => (match ris v with
        | .refl => .refl
        | .ret a b => .ret a b
        | .vis a b h => .vis a b fun v => .inl (h v))
      | .inr <| .inl v  => (match ris' v with
        | .refl => .refl
        | .ret a b => .ret a b
        | .vis a b h => .vis a b fun v => .inr <| .inl (h v))
      | .inr <| .inr ⟨_, rab, rbc⟩ => (match ris rab, ris' rbc with
        | .refl, .refl => .refl
        | .ret a b, .refl
        | .refl, .ret a b => .ret a b
        | .vis a b h, .refl => .vis a b (fun x => .inl <| h x)
        | .refl, .vis a b h => .vis a b (fun x => .inr <| .inl <| h x)
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

theorem eqSpin {a} (h : WBisim' E A a spin.dest) : a = spin.dest :=
  h.cases rfl (fun _ h => (Step.not_spin h).elim) (fun _ h => (Step.not_spin h).elim)

theorem eqSpin' {a} (h : WBisim' E A a (.tau spin)) : a = (.tau spin) :=
  h.cases rfl (fun _ h => (Step.not_spin' h).elim) (fun _ h => (Step.not_spin' h).elim)

theorem tau {a} : WBisim' E A (Base.tau a) a.dest := ⟨
  (fun a b => Nonempty (EStep a b)),
  fun {a b} ⟨ha⟩ => by
    rcases Step.no_middle b with (rfl|⟨_, ⟨h⟩⟩|⟨_,_,_, ⟨h⟩⟩)
    · rw [←spin.dest_eq] at ha
      obtain rfl := ha.spin
      rw [spin.dest_eq]
      exact .refl
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

infix:100 " ≈ " => WBisim

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

end WBisim

end Sme.ITree


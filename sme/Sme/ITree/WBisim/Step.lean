import Sme.ITree.Defs
import Sme.ITree.Combinators
import Sme.ITree.Monad

namespace Sme

universe u v

variable {E : Type u → Type u} {A B C : Type _}

namespace ITree

/-- Given Some sequence of taus, they are related to the first productive value
  Step (tau (tau (r))) r
-/
@[grind]
inductive Step : Base E (ITree E A) A → Base E (ITree E A) A → Type _
  | tau {a b} : Step a.dest b → Step (.tau a) b
  | ret {v} : Step (.ret v) (.ret v)
  | vis {e k} : Step (.vis e k) (.vis e k)

namespace Step

def depth {a b : Base E (ITree E A) _} : Step a b → Nat
  | .tau h => (depth h).succ
  | _ => 0

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

@[simp]
theorem no_step_eq {a} :
    (∀ (x : Base E (ITree E B) B), IsEmpty (Step a x))
    = (a = .tau spin) := propext {
  mp h := not_step' fun h' => (h _).false h'
  mpr h _ := h ▸ ⟨fun h => not_spin' h⟩
}


@[simp]
theorem depth0 {a b : Base E (ITree E A) _} (h : Step a b) 
    : (depth h = 0) = (a = b) := propext {
  mp h' := by
    unfold depth at h'
    split at h'
    · contradiction
    · simp_all
      grind
  mpr := by
    rintro rfl
    cases h
    <;> simp only [depth, Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero, and_false]
    rename_i h
    exact tau_rhs h
}

end Step

/--
  A collection of tau's between two values.
  EStep (tau (tau r)) (tau r)
-/
inductive EStep : Base E (ITree E A) A → Base E (ITree E A) A → Type _
  | tau {a b} : EStep a.dest b → EStep (.tau a) b
  | refl a : EStep a a

def Step.toEStep {a b : Base E _ A} : Step a b → EStep a b
  | .vis | .ret => .refl _
  | .tau h => .tau (toEStep h)

namespace EStep

def depth {a b : Base E (ITree E A) _} : EStep a b → Nat
  | .tau h => (depth h).succ
  | .refl _ => 0

def ofEq {a b : Base E (ITree E A) _} (h : a = b) : EStep a b := h ▸ .refl _
@[simp]
theorem ofEq_depth {a b : Base E (ITree E A) _} (h : a = b) : (ofEq h).depth = 0 := by
  subst h
  rfl

def trans : {a b c : Base E (ITree E A) A}
    → EStep a b → EStep b c → EStep a c
  | _,_,_, .refl _, .refl _ => .refl _
  | _,_,_, .refl _, .tau h
  | _,_,_, .tau h , .refl _ => .tau h
  | _,_,_, .tau a, .tau b => .tau <| trans a (.tau b)


@[simp]
theorem trans_depth : {a b c : Base E (ITree E A) A}
    → (ha : EStep a b) → (hb : EStep b c) 
    → (ha.trans hb).depth = ha.depth + hb.depth
  | _,_,_, .refl _, .refl _ => rfl
  | _,_,_, .refl _, .tau h
  | _,_,_, .tau h , .refl _ => by
    simp [trans, EStep.depth]
  | _,_,_, .tau ha, .tau hb => by
    simp [trans, EStep.depth, trans_depth ha (.tau hb)]
    omega

def step_comp {a b c : Base E _ A} : EStep a b → Step b c → Step a c
  | .refl _, v => v
  | .tau h, ha => .tau (step_comp h ha)

def comp_step {a b c : Base E _ A} (ha : Step a b) : EStep b c → Step a c
  | .refl _ => ha
  | .tau _ => (Step.tau_rhs ha).elim

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

def eqSpin_mpr {a} (h : a = .tau spin) : EStep (.tau (spin : ITree E A)) a:= h ▸ .refl _
def spinEq_mpr {a} (h : a = .tau spin) : EStep a (.tau (spin : ITree E A)) := h ▸ .refl _

def middle : {a c d : Base E _ A} → EStep a c → EStep a d → (EStep d c ⊕ EStep c d)
  | _, _, _, .refl _, h => .inr h
  | _, _, _, .tau h', .refl _ => .inl <| .tau h'
  | _, _, _, .tau h', .tau h => middle h' h

def meet {a b c : Base E _ A} : EStep a b → Step a c → Step b c
  | .tau h, .tau h' => meet h h'
  | .refl _, v => v

@[simp]
theorem meet_depth {a b c : Base E _ A}
    : (ha : EStep a b) → (hb : Step a c)
    → (ha.meet hb).depth = hb.depth - ha.depth
  | .tau ha, .tau hb => by
    have := meet_depth ha hb
    simp [depth, meet, this, Step.depth]
  | .refl _, _ => by
    rfl

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

noncomputable def toRetStep' {v} {a : Base E _ A}
    (h : EStep a (.ret v)) : Step a (.ret v) :=
  Classical.choice <| toRetStep h

theorem toVisStep {X e k} {a : Base E _ A}
    (h : EStep a (.vis (e : E X) k)) : Nonempty (Step a (.vis e k)) := by 
  rcases Step.no_middle a with (rfl|⟨w,⟨p⟩⟩|⟨_,_,_,⟨p⟩⟩)
  · have := EStep.eqSpin h
    contradiction
  · cases meet h p
  · cases meet h p
    exact ⟨p⟩

noncomputable def toVisStep' {X e k} {a : Base E _ A}
    (h : EStep a (.vis (e : E X) k)) : Step a (.vis e k) :=
  Classical.choice <| toVisStep h

def transp_bind_map
    (f : A → ITree E B) {a b : Base E _ A}
    : EStep a b
    → EStep (bind_map f a) (bind_map f b)
  | .tau h => .tau <| dest_bind ▸ transp_bind_map f h
  | .refl _ => .refl _

def tau' {a : Base E _ A} {b}
    (h : EStep a (.tau b))
    : EStep a b.dest :=
  .trans h <| .tau <| .refl _

@[simp]
theorem depth_tau' {a : Base E _ A} {b}
    (h : EStep a (.tau b))
    : h.tau'.depth = h.depth + 1 := by simp [tau', depth]

end Sme.ITree.EStep

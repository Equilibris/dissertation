import Sme.ITree.Defs
import Sme.ITree.Bisim

namespace Sme.ITree

universe u v

variable {E : Type u → Type u} {A B C : Type (u + 1)}

section functor

def map (f : A → B) : ITree E A → ITree E B :=
  (corec ((fun
    | .tau v => .tau v
    | .ret v => .ret (f v)
    | .vis e f => .vis e f
  ) ∘ ITree.dest))

@[simp]
theorem dest_map {i : ITree E A} {f : A → B} : dest (map f i) = i.dest.map (map f) f := by
  simp [map, dest_corec]; rw [←map]; cases i.dest <;> rfl

@[simp]
theorem mk_map {i : Base E (ITree E A) A} {f : A → B} : (map f (mk i)) = mk (i.map (map f) f) := by
  refine dest_eq ?_
  simp only [dest_map, mk_dest]

instance : Functor (ITree E) where
  map := map

@[simp]
theorem id_map (x : ITree E A) : x.map id = x := by
  ext
  refine ⟨(· = ·.map (map id) id), ?_, dest_map⟩
  rintro _ x rfl
  cases x
  · exact .tau dest_map
  · exact .ret
  · exact .vis fun _ => dest_map

instance : LawfulFunctor (ITree E) where
  id_map := id_map
  map_const := rfl
  comp_map g h x := by
    change map _ _ = map _ (map _ _)
    ext
    use (∃ y, · = Base.map (map (h ∘ g)) (h ∘ g) y ∧ · = Base.map (map h) h (Base.map (map g) g y))
    simp only [dest_map]
    refine ⟨?_, ⟨_, rfl, rfl⟩⟩
    rintro a b ⟨y, rfl, rfl⟩
    cases y
    · refine .tau ?_
      simp only [dest_map]
      exact ⟨_, rfl, rfl⟩
    · exact .ret
    · refine .vis ?_
      simp
      intro _
      refine ⟨_, rfl, rfl⟩

end functor

def bind (it : ITree E A) (f : A → ITree E B) : ITree E B :=
  .corec
    (body ∘ Sum.map ITree.dest ITree.dest)
    (.inl it : ITree E A ⊕ ITree E B)
where
  body
    | .inl (.tau v) => .tau (.inl v)
    | .inr (.tau v) => .tau (.inr v)
    | .inl (.ret v) => (f v).dest.map Sum.inr id
    | .inr (.ret v) => .ret v
    | .inr (.vis e f) => .vis e (Sum.inr ∘ f)
    | .inl (.vis e f) => .vis e (Sum.inl ∘ f)

abbrev subst (f : A → ITree E B) (it : ITree E A) : ITree E B := bind it f

@[simp]
theorem corec_bind
    {f : A → ITree E B} {r}
    : corec (bind.body f ∘ Sum.map dest dest) (Sum.inr r) = r := by
  ext
  dsimp [Bisim]
  simp only [dest_corec, Function.comp_apply, Sum.map_inr]
  refine ⟨
    (· = (Base.map (corec (bind.body f ∘ Sum.map dest dest)) id ∘ bind.body f ∘ Sum.inr) ·),
    ?_,
    rfl
  ⟩
  rintro _ a rfl
  cases a
  · refine .tau ?_
    simp
  · exact .ret
  · refine .vis fun _ => ?_
    simp

@[simp]
theorem corec_bind' {f : A → ITree E B}
    : corec (bind.body f ∘ Sum.map dest dest) ∘ Sum.inr  = id := by
  funext x
  simp

def bind_map (f : A → ITree E B) : Base E (ITree E A) A → Base E (ITree E B) B
  | .tau v => .tau <| bind v f
  | .ret v => (f v).dest
  | .vis e v => .vis e ((bind · f) ∘ v)

namespace bind_map

variable (f : A → ITree E B)

@[simp]
theorem tau {v} : bind_map f (.tau v) = .tau (bind v f) := rfl
@[simp]
theorem ret {v} : bind_map f (.ret v) = (f v).dest := rfl

end bind_map

@[simp]
theorem dest_bind
    {i : ITree E A} {f : A → ITree E B}
    : dest (bind i f)
    = bind_map f i.dest := by
  simp [bind, dest_corec, bind_map]
  cases i.dest
  any_goals rfl
  simp [bind.body, Base.map_map]
  cases (f _).dest
  <;> simp [Base.map]

@[simp]
theorem mk_bind {i : Base E (ITree E A) A} {f : A → B} : (map f (mk i)) = mk (i.map (map f) f) := by
  refine dest_eq ?_
  simp only [dest_map, mk_dest]

instance : Monad (ITree E) where
  bind := bind
  pure := .ret

theorem pure_bind (x : A) (f : A → ITree E B)
    : (ret x).bind f = f x := by
  refine dest_eq ?_
  rw [bind, dest_corec]
  simp [bind.body]
  cases (f x).dest
  · simp [Base.map]
  · rfl
  · rfl

theorem bind_assoc {x : ITree E A} {f : A → ITree E B} {g : B → ITree E C}
    : (x.bind f).bind g = x.bind ((fun x ↦ x.bind g) ∘ f) := by
  ext
  simp only [Bisim, dest_bind]
  refine ⟨
    (fun a b =>
      a = b ∨
      ∃ y : ITree _ _,
        (bind_map g ∘ bind_map f) y.dest = a ∧ bind_map (subst g ∘ f) y.dest = b),
    ?_,
    .inr ⟨_, rfl, rfl⟩
  ⟩
  rintro a b (rfl|⟨y, rfl, rfl⟩)
  · cases a
    · exact .tau (.inl rfl)
    · exact .ret
    · exact .vis (fun _ =>.inl rfl)
  rcases y.dest with (_|t|_)
  · refine .tau ?_
    simp only [Function.comp_apply, dest_bind]
    refine .inr ⟨_, rfl, rfl⟩
  case vis =>
    refine .vis ?_
    simp [Function.comp_apply, dest_bind]
    refine fun _ => .inr ⟨_, rfl, rfl⟩
  simp
  rcases (f t).dest with (r|t'|_)
  · refine .tau (.inl rfl)
  case vis =>
    refine .vis fun _ => (.inl rfl)
  simp
  conv => rhs; simp [Base.ret, bind_map]
  rcases (g t').dest with (r|_|_)
  · refine .tau (.inl rfl)
  · exact .ret
  · exact .vis fun _ => .inl rfl

theorem bind_pure_comp
    {f : A → B}
    {x : ITree E A}
    : x.bind (ret ∘ f) = map f x := by
  ext
  simp only [Bisim, dest_bind, dest_map]
  refine ⟨
    (∃ y : ITree _ _, bind_map (.ret ∘ f) y.dest = · ∧ Base.map (map f) f y.dest = ·),
    ?_,
    ⟨_, rfl, rfl⟩
  ⟩
  rintro a b ⟨y, rfl, rfl⟩
  cases y.dest
  · refine .tau ?_
    simp only [dest_bind, dest_map]
    refine ⟨_, rfl, rfl⟩
  · simp only [bind_map, Function.comp_apply, dest_ret]
    exact .ret
  · refine .vis fun _ => ?_
    simp only [Function.comp_apply, dest_bind, dest_map]
    refine ⟨_, rfl, rfl⟩

@[simp] theorem bind_map_left (f : A → B) (x : ITree E A) (g : B → ITree E C) :
    ((x.map f).bind fun b => g b) = (x.bind fun a => g (f a)) := by
  rw [← bind_pure_comp, bind_assoc]
  unfold Function.comp
  conv => lhs; rhs; intro x; simp [pure_bind]

instance : LawfulMonad (ITree E) where
  pure_bind := pure_bind
  bind_assoc x f g := bind_assoc
  bind_pure_comp {A B} f x := bind_pure_comp
  bind_map f x := rfl
  seqLeft_eq x y:= by
    change x.bind (y.bind <| .ret ∘ Function.const _ ·) = bind (map _ _) (map · y)
    conv => lhs; rhs; intro i; rw [bind_pure_comp]
    rw [bind_map_left]
  seqRight_eq x y := by
    change x.bind _ = bind (map _ _) (map · y)
    rw [bind_map_left]
    conv => rhs; rhs; intro i; simp [LawfulFunctor.id_map]
  pure_seq g x := by
    change bind (.ret _) _ = _
    rw [pure_bind]

@[simp]
theorem vis_bind {X} {e : E X} {f : _ → ITree E B} {k : X → ITree E A}
    : bind (.vis e k) f = .vis e (subst f ∘ k) := by
  refine dest_eq ?_
  simp [dest_bind, bind_map]

@[simp]
theorem tau_bind {f : _ → ITree E B} {a : ITree E A} : bind (.tau a) f = .tau (bind a f) := by
  refine dest_eq ?_
  simp

@[simp]
theorem ret_bind {f : _ → ITree E B} {a : A} : bind (.ret a) f = f a := by
  refine dest_eq ?_
  simp

end Sme.ITree

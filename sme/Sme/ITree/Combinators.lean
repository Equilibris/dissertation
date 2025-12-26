import Sme.ITree.Defs
import Sme.ITree.Bisim
import Sme.ITree.Monad

namespace Sme.ITree

universe u v

variable {E : Type u → Type u} {A B C : Type (u + 1)}

def iter (it : A → ITree E (A ⊕ B)) (v : A) : ITree E B :=
  .corec (body ∘ dest) (it v)
where
  body
    -- Using deep-thunk we should be able to remove this tau,
    -- thereby getting a strong equality between iter and bind
    -- but this will require developing the theory of deep-thunks a bit further
    | .ret (.inl v) => .tau (it v)
    | .ret (.inr v) => .ret v
    | .tau v => .tau v
    | .vis e f => .vis e f

def loop (it : C ⊕ A → ITree E (C ⊕ B)) : A → ITree E B :=
  iter (do match ← it · with
    | .inl c => return .inl <| .inl c
    | .inr v => return .inr <| v
  ) ∘ Sum.inr

theorem iter_eq {it : A → ITree E (A ⊕ B)} {v : A}
    : iter it v = bind (it v) (Sum.elim (ITree.tau ∘ iter it) .ret) := by
  dsimp [iter]
  ext
  simp [Bisim]
  refine ⟨
    (fun a b => a = b ∨ ∃ y : ITree _ _, 
        a = (Base.map (corec (iter.body it ∘ dest)) id (iter.body it y.dest)) 
      ∧ b = (bind_map (Sum.elim (tau ∘ iter it) ret) y.dest)),
    ?_,
    .inr ⟨_, rfl, rfl⟩
  ⟩
  rintro x _ (rfl|⟨w, rfl, rfl⟩)
  · exact match x with
      | .ret _ => .ret
      | .tau _ => .tau <| .inl rfl
      | .vis _ _ => .vis fun _ => .inl rfl
  rcases w.dest with (_|t|_)
  · simp only [Base.map, iter.body, id_eq, bind_map.tau]
    refine .tau <| .inr ?_
    simp only [dest_corec, Function.comp_apply, dest_bind]
    exact ⟨_, rfl, rfl⟩
  · rcases t
    · simp only [iter.body, bind_map.ret, Sum.elim_inl, Function.comp_apply, dest_tau]
      refine .tau <| .inl rfl
    · simp only [bind_map.ret, Sum.elim_inr, dest_ret]
      exact .ret
  · simp [Base.map, iter.body]
    refine .vis fun v => .inr ?_
    simp only [dest_corec, Function.comp_apply, dest_bind]
    exact ⟨_, rfl, rfl⟩

def spin : ITree E A := .corec (fun _ => .tau .unit) Unit.unit

namespace spin

@[simp]
theorem dest_eq : (spin : ITree E A).dest = .tau spin := by
  simp [spin, Base.map]

@[simp]
theorem bind_eq {f : A → ITree E B} : bind spin f = spin := by
  ext
  simp [Bisim]
  refine ⟨
    fun a b => .tau (bind spin f) = a ∧ Base.tau spin = b ,
    ?_,
    ⟨rfl, rfl⟩,
  ⟩
  rintro a b ⟨rfl, rfl⟩
  exact .tau ⟨by simp, dest_eq.symm⟩

@[simp]
theorem map_eq {f : A → B} : map f (spin : ITree E A) = spin := by
  ext
  simp [Bisim]
  refine ⟨
    fun a b => .tau (map f spin) = a ∧ Base.tau spin = b ,
    ?_,
    ⟨rfl, rfl⟩,
  ⟩
  rintro a b ⟨rfl, rfl⟩
  refine .tau ?_
  simp
  rfl

end spin

abbrev ignore : ITree E A → ITree E PUnit := map (Function.const _ PUnit.unit)

def trigger {V} : E V → ITree E (PLift V) := (.vis · (.ret ∘ PLift.up))

def forever (t : ITree E A) : ITree E B := iter (map (Function.const _ (.inl t))) t

def burn : Nat → ITree E A → ITree E A
  | 0 => id
  | n+1 => (match dest · with
    | .ret t => .ret t
    | .tau t => burn n t
    | .vis e k => .vis e k)

end Sme.ITree


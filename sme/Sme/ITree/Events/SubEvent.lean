import Sme.ITree.Defs

namespace Sme

universe u v w

class SubEvent (E : semiOutParam (Type u → Type u)) (F : (Type u → Type u)) where
  inj : ∀ {A : Type u}, E A → F A

infix:20 " -< " => SubEvent

namespace SubEvent

instance refl (E : Type u → Type u) : E -< E where
  inj := id

instance trans (E F G : Type u → Type u)
    [ef : E -< F] [fg : F -< G] : E -< G where
  inj {_} := fg.inj ∘ ef.inj

end SubEvent

def subevent {E F : Type u → Type u} [SubEvent E F] {A : Type u}
    (e : E A) : F A := SubEvent.inj e

inductive RSum (E F : Type u → Type u) (A : Type u) : Type u
  | inl (e : E A) : RSum E F A
  | inr (f : F A) : RSum E F A

infixr:30 " ⊕, " => RSum

instance {E F : Type u → Type u} : E -< E ⊕, F := ⟨.inl⟩
instance {E F : Type u → Type u} : E -< F ⊕, E := ⟨.inr⟩
instance {E F G H : Type u → Type u} [E -< G] [F -< H] : E ⊕, F -< G ⊕, H where
  inj | .inl x => .inl <| subevent x | .inr x => .inr <| subevent x

instance (priority := 10) {E F : Type u → Type u} : E ⊕, F -< F ⊕, E where
  inj | .inl x => .inr x | .inr x => .inl x

instance (priority := 20) {E F G : Type u → Type u} : (E ⊕, F) ⊕, G -< E ⊕, F ⊕, G where
  inj
    | .inl <| .inl x => .inl x
    | .inl <| .inr x => .inr <| .inl x
    | .inr x         => .inr <| .inr x

instance {E F : Type u → Type u}
    [Functor E] [Functor F]
    : Functor (RSum E F) where
  map f
  | .inl e => .inl (f <$> e)
  | .inr e => .inr (f <$> e)

def trigger {E F : Type u → Type u} [SubEvent E F] {A : Type _}
    (e : E A) : ITree F A :=
  .vis (subevent e) .ret

theorem trigger_vis
    {E F : Type u → Type u} [SubEvent E F] {A : Type u} (e : E A)
    : (trigger e).dest = .vis (subevent e : F A) .ret := by
  simp [trigger]

@[simp]
theorem subevent_eq_inj {E F : Type u → Type u} [SubEvent E F] {A : Type u}
    (e : E A) : SubEvent.inj e = (subevent e : F A) := rfl

end Sme

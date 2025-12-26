import Sme.ITree.Defs

namespace Sme

universe u v w

class SubEvent (E : Type u → Type u) (F : outParam (Type u → Type u)) where
  inj : ∀ {A : Type u}, E A → F A

infix:50 " -< " => SubEvent

namespace SubEvent

instance refl (E : Type u → Type u) : SubEvent E E where
  inj := id

instance trans (E F G : Type u → Type u)
    [ef : SubEvent E F] [fg : SubEvent F G] : SubEvent E G where
  inj {_} := fg.inj ∘ ef.inj

end SubEvent

inductive RSum (E F : Type u → Type u) (A : Type u) : Type u
  | inl (e : E A) : RSum E F A
  | inr (f : F A) : RSum E F A

instance
    (E F : Type u → Type u)
    [Functor E]
    [Functor F] : Functor (RSum E F) where
  map f
  | .inl e => .inl (f <$> e)
  | .inr e => .inr (f <$> e)

def trigger {E F : Type u → Type u} [SubEvent E F] {A R : Type _}
    (e : E A) : ITree F R :=
  ITree.vis (SubEvent.inj e) ITree.ret

-- Subevent injection function
def subevent {E F : Type u → Type u} [ReRSum E F] {A : Type u}
    (e : E A) : F A := ReRSum.inj e

-- Lemmas about ReRSum

-- Trigger preserves the structure
theorem trigger_vis {E F : Type u → Type u} [ReRSum E F] {A R : Type u}
    (e : E A) :
    (trigger e : ITree F R).dest = ITree.Base.vis (ReRSum.inj e) ITree.ret := by
  simp [trigger, ITree.dest_vis]

-- Subevent is just the injection
theorem subevent_eq_inj {E F : Type u → Type u} [ReRSum E F] {A : Type u}
    (e : E A) :
    subevent e = ReRSum.inj e := rfl

-- Composition laws for ReRSum
theorem ReRSum.inj_comp {E F G : Type u → Type u} [ReRSum E F] [ReRSum F G] [ReRSum E G]
    {A : Type u} (e : E A) :
    @ReRSum.inj E G _ e = @ReRSum.inj F G _ (@ReRSum.inj E F _ e) := rfl

-- RSum injections
theorem sum1_inj {E F : Type u → Type u} {A : Type u} (e : E A) :
    sum1 e = RSum.inl e := rfl

theorem sum2_inj {E F : Type u → Type u} {A : Type u} (f : F A) :
    sum2 f = RSum.inr f := rfl

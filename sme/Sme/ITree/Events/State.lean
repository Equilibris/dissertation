import Sme.ITree.Defs
import Sme.ITree.Bisim
import Sme.ITree.Monad
import Sme.ITree.Combinators
import Sme.ITree.MonadIter
import Sme.ITree.Events.Empty

namespace Sme.ITree

universe u v w

inductive StateE (S : Type u) : Type u → Type u
  | get : StateE S S
  | put : S → StateE S PUnit

def StateE.handle {S : Type u} {E}
    : StateE S ↝ (StateT (PLift S) (ITree E) ∘ PLift) := fun
  | _, .get => StateT.get
  | _, .put v => fun _ => pure ⟨.up .unit, .up v⟩

instance {σ : Type u} {M : Type _ → Type _} [Iter M] [Functor M]
    : Iter (StateT σ M) where
  iter f a s := Iter.iter (fun ⟨a, s⟩ => (fun
    | ⟨.inl x, y⟩ => .inl ⟨x, y⟩
    | ⟨.inr x, y⟩ => .inr ⟨x, y⟩
    ) <$> f a s) (Prod.mk a s)

end Sme.ITree


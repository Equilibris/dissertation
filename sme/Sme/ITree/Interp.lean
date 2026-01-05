import Sme.ITree.Defs
import Sme.ITree.Bisim
import Sme.ITree.Monad
import Sme.ITree.Combinators

namespace Sme.ITree

universe u v w

class Iter (M : Type u → Type _) where
  iter {A B : Type u} : (A → M (A ⊕ B)) → A → M B

instance {E : Type _ → Type _} : Iter (ITree E) where
  iter := ITree.iter

def interp {E : Type u → Type u} {M : Type (u + 1) → Type _}
    [Monad M] [Iter M]
    (inp : E ↝ (M ∘ PLift))
    : ITree E ↝ M := fun _ v =>
  Iter.iter (fun
    | .ret x => pure <| .inr x
    | .vis e k => (.inl ∘ ITree.dest ∘ k ∘ PLift.down) <$> inp _ e
    | .tau x => pure <| .inl x.dest) v.dest

instance {σ : Type u} {M : Type _ → Type _} [Iter M] [Functor M]
    : Iter (StateT σ M) where
  iter f a s := Iter.iter (fun ⟨a, s⟩ => (fun
    | ⟨.inl x, y⟩ => .inl ⟨x, y⟩
    | ⟨.inr x, y⟩ => .inr ⟨x, y⟩
    ) <$> f a s) (Prod.mk a s)

end Sme.ITree


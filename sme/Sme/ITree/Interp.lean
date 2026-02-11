import Sme.ITree.Defs
import Sme.ITree.Bisim
import Sme.ITree.Monad
import Sme.ITree.Combinators
import Sme.ITree.MonadIter

namespace Sme.ITree

universe u v w

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

/- br 2  (br 2 (a, b), br 2 (c, d)) ≈ br 4 (a, b, c, d) ≈? br 4 (b, c, d, a)  -/
/- Strong → Eq -/

end Sme.ITree


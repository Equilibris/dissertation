import Sme.ITree.Defs
import Sme.ITree.Bisim
import Sme.ITree.Monad

namespace Sme.ITree

def interp {M E : Type _ → Type _} (inp : ∀ X, E X → M X) : ∀ X, ITree E (PLift X) → M X :=
  sorry


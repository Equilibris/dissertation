import CoinductivePredicates
import Sme.ITree.Defs
import Sme.ITree.Combinators

namespace Sme

universe u v

variable {E : Type u → Type u} {A B C : Type _}

def KTree (E : Type u → Type u) (A B : Type _) : Type _ := A → ITree E B

namespace KTree

open ITree

def id (A : Type _) : KTree E A A := .ret
def comp (a : KTree E A B) (b : KTree E B C) : KTree E A C := subst b ∘ a

end KTree

end Sme


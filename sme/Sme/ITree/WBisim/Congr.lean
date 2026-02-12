import CoinductivePredicates
import Sme.ITree.Defs
import Sme.ITree.Combinators
import Sme.ITree.KTree
import Sme.ITree.WBisim.Step
import Sme.ITree.WBisim.Defs

namespace Sme.ITree.WBisim

universe u v
variable {E : Type u → Type u} {A B C : Type _} {X : Type u} {a b : ITree E A}

theorem tau_congr
    (h : a ≈ b)
    : ITree.tau a ≈ ITree.tau b := calc
  a.tau
    ≈ a     := tau
  _ ≈ b     := h
  _ ≈ b.tau := tau.symm

theorem vis_congr {e : E X} {k1 k2 : KTree E X A} (h : k1 ≈ₖ k2)
    : ITree.vis e k1 ≈ .vis e k2 :=
  vis (e := e) (dest_vis ▸ Step.vis) (dest_vis ▸ Step.vis) h

end Sme.ITree.WBisim

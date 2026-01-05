import Sme.ITree.Defs
import Sme.ITree.Bisim
import Sme.ITree.Monad
import Sme.ITree.Combinators

namespace Sme.ITree

universe u v w

inductive StateE (S : Type u) : Type u → Type u
  | get : StateE S S
  | put : S → StateE S PUnit

def StateE.handle {E} {S} : StateE S ↝ StateT S (ITree E) := fun
  | _, .get => StateT.get
  | _, .put v => StateT.set v

def StateE.interp {S E} : ITree (StateE S) ↝ StateT S (ITree E) :=
  fun _ x s => ITree.iter (fun
    | ⟨s, .ret v⟩ => .ret <| .inr ⟨v, s⟩
    | ⟨s, .tau v⟩ => .ret <| .inl ⟨s, v.dest⟩
    | ⟨s, .vis e v⟩ => ITree.map (fun ⟨a, s⟩ => .inl ⟨s, (v a).dest⟩) <| handle _ e s)
    (Prod.mk s x.dest)

end Sme.ITree


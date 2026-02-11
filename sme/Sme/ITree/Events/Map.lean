import Sme.ITree.Defs
import Sme.ITree.Bisim
import Sme.ITree.Monad
import Sme.ITree.Combinators
import Sme.ITree.MonadIter
import Sme.ITree.Events.State
import Std.Data.ExtHashMap.Basic

namespace Sme.ITree

universe u v w

inductive MapE (K V : Type u) : Type u → Type u
  | insert : K → V → MapE K V PUnit
  | get : K → MapE K V (Option V)
  | getD : K → V → MapE K V V
  | erase : K → MapE K V PUnit

def MapE.handle {K V : Type u} [BEq K] [EquivBEq K] [Hashable K] [LawfulHashable K]
    : MapE K V ↝ (StateT (PLift (Std.ExtHashMap K V)) (ITree EmptyE) ∘ PLift) := fun
  | _, .insert k v => fun hm => pure ⟨.up .unit, .up <| hm.down.insert k v⟩
  | _, .get k => fun hm => pure ⟨.up <| hm.down.get? k, hm⟩
  | _, .getD k v => fun hm => pure ⟨.up <| hm.down.getD k v, hm⟩
  | _, .erase k => fun hm => pure ⟨.up .unit, .up <| hm.down.erase k⟩
  /- | _, .put v => fun _ => pure ⟨.up .unit, .up v⟩ -/

end Sme.ITree

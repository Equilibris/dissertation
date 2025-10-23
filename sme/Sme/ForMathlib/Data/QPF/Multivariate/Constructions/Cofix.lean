import Mathlib.Data.QPF.Multivariate.Constructions.Cofix

universe u v x y

namespace MvQPF

variable {n : Nat} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F]

def corecF' {α : TypeVec n} {β : Type u} (g : β → F (α.append1 β)) : β → q.P.M α :=
  MvPFunctor.M.corec _ fun x => repr (g x)

end MvQPF


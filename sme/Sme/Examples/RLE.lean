import Sme.M.Futu
import Sme.Examples.Stream

def RLE_base {α} [DecidableEq α]
    (n : Nat) (s : SS α)
    : SS (α × Nat) := 
  .corec' sorry (Prod.mk Nat.zero s.dest)

def RLE_decode {α} (s : SS (α × Nat))
    : SS α :=
  .corec' f s.dest
where
  f | ⟨⟨v, 0  ⟩, r⟩ => SS.mk v r.dest
    | ⟨⟨v, n+1⟩, r⟩ => SS.mk v ⟨⟨v, n⟩, r⟩

open Sme (Free)

def RLE_decode' {α} : SS (α × Nat) → SS α := Free.futu' f where
  f x :=
    have ⟨⟨v, n⟩, r⟩ := x.dest
    iter v r n
  iter v r
    | 0   => SS.mk v <| .recall r
    | n+1 => SS.mk v <| .cont' <| iter v r n


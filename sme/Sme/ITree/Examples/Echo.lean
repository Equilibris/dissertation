import Sme.ITree.Interp
import Sme.ITree.Events.State

open Sme ITree

def echo : ITree (StateE Nat) PEmpty :=
  .iter (fun _ =>
    .vis .get fun v =>
    .vis (.put v) fun _ =>
    .ret <| .inl .unit
  ) Unit.unit

#check interp StateE.handle _ echo


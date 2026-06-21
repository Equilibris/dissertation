import Sme.Macro.Derive

namespace Sme

universe u

set_option format.width 0

inductive Sum (n : Nat) (A B : Type u) : Type u
  | inl (v : Fin n → Prop) (v : Bool → A) : Sum n A B
  | inr : B → Sum n A B
deriving EquivP

inductive Deps : Type u
  | s : Nat → Deps
  | z
deriving EquivP

inductive Nat : Type u
  | s : Nat → Nat
  | z
deriving EquivP

inductive List (A : Type u) : Type u
  | s : A → List A → List A
  | z
deriving EquivP


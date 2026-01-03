
inductive ITIO : Type → Type
  | Inp : ITIO Nat
  | Out : Nat → ITIO Unit


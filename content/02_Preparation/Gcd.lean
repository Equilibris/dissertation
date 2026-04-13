set_option trace.Compiler.result true in
@[semireducible]
def gcd (a b : Nat) : Nat :=
  if h' : b = 0 then a
  else
    have : a % b < b := Nat.mod_lt a
      (Nat.pos_of_ne_zero h')
    gcd b (a % b)
termination_by b

/--
info: def gcd._unary : (_ : Nat) ×' Nat → Nat :=
WellFounded.Nat.fix (fun x => PSigma.casesOn x fun a b => b) fun _x a =>
  PSigma.casesOn (motive := fun _x =>
    ((y : (_ : Nat) ×' Nat) → InvImage (fun x1 x2 => x1 < x2) (fun x => PSigma.casesOn x fun a b => b) y _x → Nat) →
      Nat)
    _x
    (fun a b a_1 =>
      if h' : b = 0 then a
      else
        have this := ⋯;
        a_1 ⟨b, a % b⟩ ⋯)
    a
-/
#guard_msgs in
#print gcd._unary


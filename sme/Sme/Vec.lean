import Mathlib.Data.TypeVec

universe u v w

abbrev Vec (α : Type _) (n : Nat) := (i : Fin2 n) → α

namespace Vec

variable {α : Type u}

def append1 {n} (tl : Vec α n) (hd : α) : Vec α (.succ n)
  | .fs i   => tl i
  | .fz     => hd

def nil : Vec α 0 := Fin2.elim0

variable {n}

@[simp]
theorem append1.get_fz (tl : Vec α n) (hd : α) : append1 tl hd .fz = hd := rfl
@[simp]
theorem append1.get_fs (tl : Vec α n) (hd : α) {i} : append1 tl hd (.fs i) = tl i := rfl

end Vec

syntax "!![" term,* "]" : term
syntax "!![" term ";" term,* "]" : term
macro_rules
  | `(!![])    => `(Vec.nil)
  | `(!![$x])  => `(Vec.append1 !![] $x)
  | `(!![ $xs,* , $x]) => `(Vec.append1 !![$xs,*] $x)
  | `(!![$t; ])    => `($t)
  | `(!![$t; $x])  => `(Vec.append1 $t $x)
  | `(!![$t;  $xs,* , $x]) => `(Vec.append1 !![$t; $xs,*] $x)


namespace Vec
open Lean in
def uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (Option Term × TSyntaxArray `term)
  | `(!![$x,*]) => pure ⟨.none, x⟩
  | `(!![$t; $x,*]) => pure ⟨.some t, x⟩
  | `($t) => pure ⟨.some t, ∅⟩

@[app_unexpander Vec.nil]
def nil_uex : Lean.PrettyPrinter.Unexpander
  | `($_p) => `(!![])

@[app_unexpander Vec.append1]
def append1_uex : Lean.PrettyPrinter.Unexpander
  | `($_p $l $r) => do
    match ← Vec.uex_inner l with
    | ⟨.none,   rst⟩ => `(!![$(rst.push r),* ])
    | ⟨.some t, rst⟩ => `(!![$t; $(rst.push r),* ])
  | _ => throw () -- unhandled

end Vec


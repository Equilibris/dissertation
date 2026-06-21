import Lean.Meta
import Std.Data.HashSet
import Sme.PFunctor.EquivP
import Sme.Macro.Trace

open Lean

inductive FieldT where
  | bv    : Nat → FieldT
  | const : Expr → FieldT
  | fn    : Name → Expr → FieldT → BinderInfo → FieldT
  | call  : Name → List Level → Array FieldT → FieldT
deriving Repr, BEq

namespace FieldT

open Lean Elab.Command

partial def exprToFieldT : Expr → CommandElabM FieldT
  | x@(.app _ _) => do
    have hd := x.getAppFn'
    let .const hdnm hdlv := hd |
      throwError s!"Expected bottom of app-chain to be const but got {hd}"
    let ch ← x.getAppArgs'.mapM exprToFieldT
    return .call hdnm hdlv ch
  | .bvar n => return .bv n
  | .forallE nm ty body info =>
    return .fn nm ty (←exprToFieldT body) info
  | .const nm lv => return .call nm lv #[]
  | x => return .const x

def isConst : FieldT → Bool
  | .const _ => .true
  | _ => .false

/--
  flist is the list of weather or not arguments are functorial,
  and what index they have in the functor.
-/
partial def constize (flist : List (Option Nat))
    : FieldT → FieldT
  | .bv idx => sorry
  | .const x => .const x
  | .call arg lvs rest =>
    have m := rest.map (constize flist)
    if m.all isConst then
      have := Expr.app
      .const <| sorry
    else
      .call arg lvs m
  | .fn nm ty rest info =>
    match constize (none :: flist) rest with
    | .const e => .const <| .lam nm ty e info
    | x => .fn nm ty x info

partial def exprLooseBVars (e : FieldT) (depth : Nat) (acc : Std.HashSet Nat := {}) : Std.HashSet Nat :=
  match e with
  | .const v => goe v depth acc
  | .bv _ | .sort _ => acc
  | .call _ _ arr =>
    arr.foldr (@exprLooseBVars · depth) acc
  | .fn _ e ft _ =>
    have acc := goe e depth acc
    exprLooseBVars ft depth.succ acc
where
  goe (e : Expr) (depth : Nat) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
    if e.looseBVarRange ≤ depth then acc
    else match e with
    | .bvar i           =>
        if i >= depth then acc.insert (i - depth) else acc
    | .app f a          =>
        goe a depth (goe f depth acc)
    | .lam _ t b _      =>
        goe b (depth + 1) (goe t depth acc)
    | .forallE _ t b _  =>
        goe b (depth + 1) (goe t depth acc)
    | .letE _ t v b _   =>
        goe b (depth + 1) (goe v depth (goe t depth acc))
    | .mdata _ inner    => goe inner depth acc
    | .proj _ _ inner   => goe inner depth acc
    | _                 => acc

end FieldT

structure Field where
  name : Option Name
  ty : FieldT
  binderKind : BinderInfo

  loc : Syntax
deriving Repr, BEq

structure ConstructorView where
  fields : Array Field
  name : Name

  loc : Syntax
deriving Repr, BEq

structure DataView where
  constructors : Array ConstructorView

  loc : Syntax
deriving Repr, BEq




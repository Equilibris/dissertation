import Lean.Meta
import Sme.PFunctor.EquivP
import Sme.Macro.Trace
import Sme.Macro.View

open Lean Elab.Command

namespace Sme

deriving instance Repr for ConstantVal, InductiveVal, ConstructorVal

structure VInfo (X : Type) where
  name : Name
  type : X
  binderInfo : BinderInfo
deriving Repr

namespace VInfo

def map {A B} (f : A → B) : VInfo A → VInfo B
  | {name, type, binderInfo} => {name, type := f type, binderInfo}
def mapM {M A B} [Monad M] (f : A → M B) : VInfo A → M (VInfo B)
  | {name, type, binderInfo} => return {name, type := ← f type, binderInfo}

instance {X} [ToString X] : ToString (VInfo X) where
  toString
    | {name, type, binderInfo := .default} => s!"({name} : {type})"
    | {name, type, binderInfo := .implicit} => s!"\{{name} : {type}}"
    | {name, type, binderInfo := .instImplicit}  => s!"[{name} : {type}]"
    | {name, type, binderInfo := .strictImplicit}  => s!"⦃{name} : {type}⦄"

end VInfo

abbrev ParamInfo := VInfo Expr
abbrev FieldInfo := VInfo FieldT

def extractParameterNamesFromType
    (inp : Array ParamInfo)
    : Nat → Expr → CommandElabM (Array ParamInfo × Expr)
  | 0,   v => return ⟨inp, v⟩
  | n+1, .forallE name type body info => extractParameterNamesFromType
      (inp.push {name := name, type := type, binderInfo := info})
      n body
  | _+1, e => do
    throwError s!"Parameter {e} is not of expected type, expected series of foralls"

def extract
    (inp : Array ParamInfo)
    : Nat → Expr → CommandElabM (Array ParamInfo × Expr)
  | 0,   v => return ⟨inp, v⟩
  | n+1, .forallE name type body info => extractParameterNamesFromType
      (inp.push {name := name, type := type, binderInfo := info})
      n body
  | _+1, e => do
    throwError s!"Parameter {e} is not of expected type, expected series of foralls"

/- def exprTo -/

structure CtorInfo extends ConstructorVal where
  fields : Array FieldInfo
deriving Repr

structure Stage1 extends InductiveVal where
  paramInfo : Array ParamInfo
  ctorsInfo : List CtorInfo
deriving Repr

def transform1.ctor (name : Name) : CommandElabM CtorInfo := do
  let ctorInfo ← getConstInfoCtor name
  let ⟨_, bot⟩ ← extractParameterNamesFromType #[] ctorInfo.numParams ctorInfo.type
  let ⟨fields, _⟩ ← extractParameterNamesFromType #[] ctorInfo.numFields bot
  let fields ← fields.mapM (VInfo.mapM exprToFieldT)
  return { toConstructorVal := ctorInfo, fields }

def transform1 (name : Name) : CommandElabM Stage1 := do
  let indVal ← getConstInfoInduct name
  let ⟨paramInfo, _⟩ ← extractParameterNamesFromType #[] indVal.numParams indVal.type
  let ctorsInfo ← indVal.ctors.mapM transform1.ctor
  return {
    toInductiveVal := indVal
    paramInfo,
    ctorsInfo,
  }

def mkSmeDerive (declNames : Array Name)
    : CommandElabM Bool := do
  for name in declNames do
    let transform ← transform1 name
    /- if transform.isRec then -/
    /-   dbg_trace "Cant handle rec yet" -/
    /-   continue -/
    -- find all args that are referenced in constant values,
    -- thereby have to be dead.
    have dead := transform.ctorsInfo.map
      (·.fields.map VInfo.type
        |>.mapIdx (flip FieldT.exprLooseBVars)
        |>.foldr Std.HashSet.union {})
      |>.foldr Std.HashSet.union {}
    have fargs := transform.paramInfo.map (fun x =>
      match x.type with
      | .sort v => Option.some v
      | _ => .none
    ) |>.mapIdx (fun n i => if transform.paramInfo.size - n - 1 ∈ dead then .none else i)
    for ctor in transform.ctorsInfo do
      dbg_trace repr ctor.fields

  return true
  /- stop -/
  /- if declNames.size != 1 then return false -/
  /- let name := declNames[0]! -/
  /- have := transform1 name -/
  /- let indVal ← getConstInfoInduct name -/
  /- let ⟨x, bot⟩ ← extractParameterNamesFromType #[] indVal.numParams indVal.type -/
  /- -- Only handle types with a single constructor -/
  /- dbg_trace x -/
  /- for ctorName in indVal.ctors do -/
  /-   let ctorInfo ← getConstInfoCtor ctorName -/
  /-   let ⟨_, bot⟩ ← extractParameterNamesFromType #[] ctorInfo.numParams ctorInfo.type -/
  /-   let ⟨x, bot⟩ ← extractParameterNamesFromType #[] ctorInfo.numFields bot -/
  /-   let v ← x.mapM (VInfo.mapM exprToFieldT) -/
  /-   have s := v.map VInfo.type |>.map FieldT.exprLooseBVars |>.foldr Std.HashSet.union {} -/
  /-   /- have := x.mapM  -/ -/
  /-   dbg_trace repr s -/
  /- return false -/
  /-  -/
initialize Elab.registerDerivingHandler ``Sme.EquivP mkSmeDerive


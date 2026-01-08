import Sme

open Sme

open MvPFunctor

namespace Test

def QStream.Base : MvPFunctor 2 := ⟨
  PUnit,
  fun _ _ => PUnit
⟩

def QStreamSl α := M QStream.Base (fun _ => α)
def QStreamHp α := HpLuM QStream.Base (fun _ => α)

structure QStreamBig.{u} (α : Type u) where
  corec ::
    {t : Type u}
    (functor : t → QStream.Base !![α, t])
    (obj : t)

def QStreamBig.dest {α} (x : QStreamBig α) : QStream.Base !![QStreamBig α, PLift α] :=
  have ⟨.unit, tl⟩ := x.functor x.obj
  ⟨.unit, fun
    | .fz, .unit => .up <| tl (.fs .fz) .unit
    | .fs .fz, .unit => .corec x.functor <| tl .fz .unit⟩

set_option trace.compiler.ir.result true in
section

def numsSl : QStreamSl Nat :=
  .corec _ (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero

def numsHp : QStreamHp Nat :=
  .corec' (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero

def numsBig : QStreamBig Nat :=
  QStreamBig.corec (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) 0

def QStreamBig.getNth (x : QStreamBig Nat) : Nat → Nat
  | 0 => match x.dest with
    | ⟨.unit, v⟩ => (v .fz .unit).down
  | n+1 => match x.dest with
    | ⟨.unit, v⟩ => QStreamBig.getNth (v (.fs .fz) .unit) n

def QStreamSl.getNth (x : QStreamSl Nat) : Nat → Nat
  | 0 => match x.dest with
    | ⟨.unit, v⟩ => v (.fs .fz) .unit
  | n+1 => match x.dest with
    | ⟨.unit, v⟩ => QStreamSl.getNth (v .fz .unit) n

def QStreamHp.getNth (x : QStreamHp Nat) : Nat → Nat
  | 0 => match x.dest with
    | ⟨.unit, v⟩ => v (.fs .fz) .unit
  | n+1 => match x.dest with
    | ⟨.unit, v⟩ => QStreamHp.getNth (v .fz .unit) n

end

def time (f : Unit → IO Unit) : IO Nat := do
  let pre ← IO.monoMsNow
  f ()
  let ante ← IO.monoMsNow
  return ante - pre

def runTests : IO Unit := do
  let testHp := fun n _ => do if (QStreamHp.getNth numsHp n) ≠ n then println! "NEQ!";
  let testSl := fun n _ => do if (QStreamSl.getNth numsSl n) ≠ n then println! "NEQ!";
  let testBig   := fun n _ => do if (numsBig.getNth n) ≠ n then println! "NEQ!";

  let n := 200
  let s := 10

  let sl := (List.range n).map (time ∘ testSl)
  let hp := (List.range n).map (time ∘ testHp)
  let big := (List.range n).map (time ∘ testBig)

  let runs := fun io => (List.replicate s io).mapM id

  println! "sl runs"
  let res ← runs <| sl.mapM id
  println! res

  println! "hp runs"
  let res ← runs <| hp.mapM id
  println! res

  println! "big runs"
  let res ← runs <| big.mapM id
  println! res

  return ()

def runTestsHp : IO Unit := do
  let testHp := fun n _ => do if (QStreamHp.getNth numsHp n) ≠ n then println! "NEQ!";
  let testBig   := fun n _ => do if (numsBig.getNth n) ≠ n then println! "NEQ!";

  let n := 1000
  let s := 3

  let hp := (List.range n).map (time ∘ testHp)
  let big := (List.range n).map (time ∘ testBig)

  let runs := fun io => (List.replicate s io).mapM id

  println! "hp runs"
  let res ← runs <| hp.mapM id
  println! res

  println! "big runs"
  let res ← runs <| big.mapM id
  println! res

  return ()


#time #eval  (QStreamHp.getNth  numsHp  1000000)
#time #eval  (QStreamBig.getNth numsBig 1000000)
#time #eval! (QStreamHp.getNth  numsHp  1000000)
#time #eval! (QStreamBig.getNth numsBig 1000000)

/- #eval runTests -/
/- #eval runTestsHp -/

end Test

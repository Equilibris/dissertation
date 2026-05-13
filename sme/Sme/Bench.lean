import Sme

open Sme MvPFunctor

namespace Test

def QStream.Base : MvPFunctor 2 := ⟨
  PUnit,
  fun _ _ => PUnit
⟩

def QStreamSl α := MvPFunctor.M QStream.Base (fun _ => α)
def QStreamHp α := Sme.M QStream.Base (fun _ => α)
def QStreamPreM α := PreM QStream.Base (fun _ => α)
def QStreamSM α := SM QStream.Base (fun _ => α)

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

/- set_option trace.compiler.ir.result true in -/
section

def numsSl : QStreamSl Nat :=
  .corec _ (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero

/- def numsHp : QStreamHp Nat := -/
/-   .corec' (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero -/

def numsHp : QStreamHp.{0} Nat :=
  Sme.M.corec.{0,0} (fun n => ⟨
    .up .unit,
    fun | .fz, .up .unit => .up <| .up <| n.down.succ | .fs .fz, .up .unit => n⟩)
    <| ULift.up Nat.zero

def numsPreM : QStreamPreM.{0} Nat :=
  .corec (fun n => ⟨
    .up .unit,
    fun | .fz, .up .unit => .up <| .up <| n.down.succ | .fs .fz, .up .unit => n⟩) <| .up Nat.zero

def numsSM : QStreamSM.{0} Nat :=
  .corec (fun n => ⟨
    .up .unit,
    fun | .fz, .up .unit => .up <| .up <| n.down.succ | .fs .fz, .up .unit => n⟩) <| .up Nat.zero

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

def QStreamPreM.getNth (x : QStreamPreM Nat) : Nat → Nat
  | 0 => match x.dest with
    | ⟨.up .unit, v⟩ => (v (.fs .fz) <| .up .unit).down
  | n+1 => match x.dest with
    | ⟨.up .unit, v⟩ => QStreamPreM.getNth (v .fz <| .up .unit) n

def QStreamSM.getNth (x : QStreamSM Nat) : Nat → Nat
  | 0 => match x.dest with
    | ⟨.up .unit, v⟩ => (v (.fs .fz) <| .up .unit).down
  | n+1 => match x.dest with
    | ⟨.up .unit, v⟩ => QStreamSM.getNth (v .fz <| .up .unit) n

def QStreamHp.getNth (x : QStreamHp Nat) : Nat → Nat
  | 0 => match x.dest with
    | ⟨.unit, v⟩ => v (.fs .fz) .unit
  | n+1 => match x.dest with
    | ⟨.unit, v⟩ => QStreamHp.getNth (v .fz .unit) n

end

def time (f : Unit → IO Unit) : IO Nat := do
  let pre ← IO.monoNanosNow
  f ()
  let ante ← IO.monoNanosNow
  return (ante - pre)

def runs {A} (s : Nat) (io : IO (List A)) : IO (List (List A)) :=
  (List.replicate s io).mapM id

def runTests : IO Unit := do
  let testHp   := fun n _ => do if (QStreamHp.getNth numsHp n) ≠ n then println! "NEQ!";
  let testSl   := fun n _ => do if (QStreamSl.getNth numsSl n) ≠ n then println! "NEQ!";
  let testSM   := fun n _ => do if (QStreamSM.getNth.{0} numsSM n) ≠ n then println! "NEQ!";
  let testPreM := fun n _ => do if (QStreamPreM.getNth.{0} numsPreM n) ≠ n then println! "NEQ!";
  let testBig  := fun n _ => do if (numsBig.getNth n) ≠ n then println! "NEQ!";

  let s := 3

  let n := 200
  let sl := (List.range n).map (time ∘ testSl)

  let n := 5000
  let hp   := (List.range n).map (time ∘ testHp)
  let big  := (List.range n).map (time ∘ testBig)
  let preM := (List.range n).map (time ∘ testPreM)
  let sm   := (List.range n).map (time ∘ testSM)

  /- IO.print "slRuns = " -/
  /- let res ← runs s <| sl.mapM id -/
  /- println! res -/

  IO.print "hpRuns = "
  let res ← runs s <| hp.mapM id
  println! res

  /- IO.print "bigRuns = " -/
  /- let res ← runs <| big.mapM id -/
  /- println! res -/

  IO.print "smRuns = "
  let res ← runs s <| sm.mapM id
  println! res

  IO.print "preMRuns = "
  let res ← runs s <| preM.mapM id
  println! res

  return ()

/- #eval! runTests -/
/- #eval runTestsHp -/

end Test

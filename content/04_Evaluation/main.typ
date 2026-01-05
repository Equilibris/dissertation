
== Performance between SME and PA<smevpa>

After building the equivelence,
and instantiating shrink,
we now have the ability to compare the performance between 3 representations:
The SME encoding (high performance, hpRuns),
the PA encoding (slow, slRuns),
and a hand made big implementation (bigRuns).
We compare these 3 in @perf.
In @perf we see the 3 representations specalised to infinite streams, 
the code for which can be seen in @perfcode
// TODO: Combine these to one plot

#figure(
  image("../../data/plot.png", width: 500pt),
  caption: [Performance of SME, PA, and Big representation]
)<perf>

#figure(
  ```lean
def QStream.Base : MvPFunctor 2 := ⟨
  Unit,
  fun _ _ => Unit
⟩

def QStreamSl α := M QStream.Base (fun _ => α)
def QStreamHp α := HpLuM QStream.Base (fun _ => α)

structure QStreamBig.{u} (α : Type _) where
  corec ::
    {t : Type u}
    (functor : t → Nat × t)
    (obj : t)

def numsSl : QStreamSl Nat :=
  .corec _ (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero

def numsHp : QStreamHp Nat :=
  .corec' (fun n => ⟨.unit, fun | .fz, .unit => n.succ | .fs .fz, .unit => n⟩) Nat.zero

def numsBig : QStreamBig Nat :=
  QStreamBig.corec (fun n => ⟨n, n + 1⟩) 0

def QStreamBig.getNth (x : QStreamBig Nat) : Nat → Nat
  | 0 => x.dest.fst
  | n+1 => x.dest.snd.getNth n

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
  ```
)<perfcode>


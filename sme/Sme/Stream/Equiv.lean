import Sme.Stream.PDefs
import Sme.Stream.SDefs

open PDef in
def Sme.Stream.equiv.{u} {A} : SStream.{u, u} A ≃ PStream A where
  toFun :=  PStream.corec SStream.dest
  invFun := SStream.corec PStream.dest
  left_inv _x := SStream.bisim ⟨
    fun a b => a = .corec PStream.dest (.corec SStream.dest b),
    fun {a _b} (hab : a = _) =>
      hab ▸ .step rfl rfl,
    rfl
  ⟩
  right_inv _x := PStream.bisim ⟨
    fun a b => a = .corec SStream.dest (.corec PStream.dest b),
    fun {a _b} (hab : a = _) =>
      hab ▸ .step rfl rfl,
    rfl
  ⟩

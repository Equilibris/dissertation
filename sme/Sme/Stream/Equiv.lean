import Sme.Stream.PDefs
import Sme.Stream.SDefs

open PDef

namespace Sme

universe u

variable {A : Type u}

def Stream.equiv : SStream.{u, u} A ≃ PStream A := ⟨
  PStream.corec SStream.dest,
  SStream.corec PStream.dest,
  fun _x => SStream.bisim ⟨
    fun a b => a = .corec PStream.dest (.corec SStream.dest b),
    fun {a _b} (hab : a = _) => hab ▸ .step rfl rfl,
    rfl
  ⟩,
  fun _x => PStream.bisim ⟨
    fun a b => a = .corec SStream.dest (.corec PStream.dest b),
    fun {a _b} (hab : a = _) => hab ▸ .step rfl rfl,
    rfl
  ⟩,
⟩

end Sme


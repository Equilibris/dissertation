import Sme.Stream.PDefs
import Sme.Stream.SDefs

open PDef

namespace Sme

universe u

variable {A : Type u}

def equiv : SStream A ≃ PStream A := ⟨
  .corec SStream.dest,
  .corec PStream.dest,
  fun x => SStream.bisim ⟨sorry, fun {x y} rxy => .step sorry sorry, by sorry⟩,
  fun x => PStream.bisim sorry,
⟩

end Sme


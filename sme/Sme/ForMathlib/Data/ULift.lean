
namespace ULift

universe u v w

variable {A : Type u}

@[inline]
def transliterate : ULift A → ULift A := ULift.up ∘ ULift.down

@[simp]
theorem transliterate_idempotent : transliterate ∘ transliterate = transliterate (A := A) := rfl

@[simp]
theorem transliterate_down {x : ULift A} : (ULift.transliterate x).down = x.down := rfl

@[simp]
theorem transliterate_up {x : A} : (ULift.transliterate <| .up x) = .up x := rfl

@[simp]
theorem transliterate_def_rev {x : ULift A} : ULift.up x.down = .transliterate x := rfl

@[simp]
theorem transliterate_noop {x : ULift A} : transliterate x = x := rfl


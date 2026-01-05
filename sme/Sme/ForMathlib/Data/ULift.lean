
namespace ULift

universe u v w

variable {A : Type u}

@[inline]
def transliterate : ULift A → ULift A := ULift.up ∘ ULift.down

@[simp]
theorem transliterate_idempotent : transliterate ∘ transliterate = transliterate (A := A) := rfl


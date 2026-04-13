namespace ULift

universe u v w
variable {A : Type u} {x : ULift A} {a : A}

@[inline] def transliterate : ULift.{v} A → ULift.{w} A := ULift.up ∘ ULift.down

@[simp] theorem transliterate_idempotent
    : transliterate ∘ transliterate = transliterate (A := A) := rfl
@[simp] theorem transliterate_noop
    : transliterate x = x                                    := rfl
@[simp] theorem transliterate_down
    : (ULift.transliterate x).down = x.down                  := rfl
@[simp] theorem transliterate_up
    : ULift.transliterate (.up a) = .up a                    := rfl
@[simp] theorem transliterate_def_rev
    : ULift.up x.down = .transliterate x                     := rfl

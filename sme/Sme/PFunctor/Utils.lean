import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Sme.ForMathlib.Data.ULift
import Mathlib.Control.Functor.Multivariate

universe u v w

namespace Sme

open MvPFunctor
open scoped MvFunctor

variable {n : Nat} {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

@[inline]
def transliterateMap {γ β}
    (f : β → γ)
    (x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β))
    : MvPFunctor.uLift.{u, w} P
        (TypeVec.uLift.{u, w} α ::: γ) where
  fst := .transliterate x.fst
  snd := (TypeVec.appendFun .transliterate f) ⊚ x.snd ⊚ .transliterate

@[simp]
theorem transliterateMap_comp {γ δ β}
    (g : γ → δ) (f : β → γ)
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β)}
    : transliterateMap g (transliterateMap f x) = transliterateMap (g ∘ f) x := 
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz,   _ => rfl
    | .fs _, _ => rfl

theorem transliterateMap_map {γ γ' δ β}
    (g' : α.uLift ⟹ δ) (g : γ → γ') (f : β → γ)
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β)}
    : (g' ::: g) <$$> (transliterateMap f x) = (g' ::: id) <$$> transliterateMap (g ∘ f) x := 
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz,   _ => rfl
    | .fs _, _ => rfl

@[simp]
theorem transliterateMap_eq_map {γ β}
     (f : β → γ)
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β)}
    : (transliterateMap f x) = (TypeVec.id ::: f) <$$> x :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz,   _ => rfl
    | .fs _, _ => rfl

@[simp]
theorem transliterateMap_fst
    {β γ}
    {f : β → γ}
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β)}
    : (transliterateMap f x).fst = .transliterate x.fst := rfl

@[simp]
theorem transliterateMap_snd
    {β γ}
    {f : β → γ}
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: β)}
    : (transliterateMap f x).snd = (.transliterate ::: f) ⊚ x.snd ⊚ .transliterate := rfl

@[simp]
theorem transliterateMap_snd_fz
    {β γ}
    (f : β → γ)
    (x : P.uLift (α.uLift ::: β))
    : (transliterateMap f x).snd .fz = f ∘ x.snd .fz ∘ .transliterate := rfl

-- TODO: Try to remove one or both of these and replace them with a kind of mapping
@[inline]
def transliterate
    : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β)
    → MvPFunctor.uLift.{u, max v w} P
        (TypeVec.uLift.{u, max v w} α ::: ULift.{max u w, v} β) := 
  transliterateMap ULift.transliterate

@[simp]
theorem transliterate_fst
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β)}
    : (transliterate x).fst = .transliterate x.fst := rfl

@[simp]
theorem transliterate_snd
    {x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β)}
    : (transliterate x).snd = (.transliterate ::: .transliterate) ⊚ x.snd ⊚ .transliterate := 
  rfl

@[inline, pp_with_univ]
def upMap {γ β}
    (f : β → γ)
    (x : P (α ::: β))
    : MvPFunctor.uLift.{u, w} P
        (TypeVec.uLift.{u, w} α ::: γ) :=
  ((TypeVec.id ::: f ∘ ULift.down) ⊚ .mpr TypeVec.uLift_append1_ULift_uLift) <$$> uLift_up x

@[inline, pp_with_univ]
def downMap {γ β}
    (f : β → γ)
    (x : MvPFunctor.uLift.{u, w} P
        (TypeVec.uLift.{u, w} α ::: β))
    : P (α ::: γ) :=
  uLift_down <| (.mp TypeVec.uLift_append1_ULift_uLift ⊚ (TypeVec.id ::: ULift.up ∘ f) ) <$$> x

theorem eq_downMap {β}
    (x : P.uLift (α.uLift ::: ULift β))
    : uLift_down (.mp TypeVec.uLift_append1_ULift_uLift <$$> x)
    = downMap ULift.down x := 
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

@[simp]
theorem upMap_eq_upMap {γ β}
    (f g : β → γ)
    (x y : P (α ::: β))
    : (upMap f x = upMap g y) = ((TypeVec.id ::: f) <$$> x = (TypeVec.id ::: g) <$$> y) := propext {
  mp h := by
    rcases x with ⟨hd, sx⟩
    rcases y with ⟨hdy, sy⟩
    obtain rfl : hd = hdy := (ULift.up.injEq _ _).mp <| (Sigma.ext_iff.mp h).1
    have := funext_iff.mp (eq_of_heq (Sigma.ext_iff.mp h).2)
    refine Sigma.ext rfl <| heq_of_eq <| funext₂ fun | .fz, h | .fs i, h => ?_
    <;> dsimp
    · specialize this .fz
      have := funext_iff.mp this <| .up h
      simpa [upMap] using this
    · specialize this i.fs
      have := funext_iff.mp this <| .up h
      simp only [TypeVec.append1_get_fs, upMap, TypeVec.mpr_eq_mp, map_fst, uLift_up_fst, map_snd,
        uLift_up_snd, TypeVec.comp.get, TypeVec.appendFun.get_fs, TypeVec.id.get, TypeVec.mp.get,
        Function.id_comp, TypeVec.arrow_uLift.get, Function.comp_apply, cast_eq] at this
      exact ULift.up_inj.mp this
  mpr h := by
    rcases x with ⟨hd, sx⟩
    rcases y with ⟨hdy, sy⟩
    obtain rfl : hd = hdy := (Sigma.ext_iff.mp h).1
    have := funext_iff.mp (eq_of_heq (Sigma.ext_iff.mp h).2)
    refine Sigma.ext rfl <| heq_of_eq <| funext₂ fun | .fz, h | .fs i, h => ?_
    <;> dsimp [upMap]
    · specialize this .fz
      have := funext_iff.mp this <| h.down
      simpa [upMap] using this
    · specialize this i.fs
      have := funext_iff.mp this <| h.down
      simp only [TypeVec.append1_get_fs, map_mk, upMap, TypeVec.mpr_eq_mp, map_fst, uLift_up_fst,
        TypeVec.comp.get, TypeVec.appendFun.get_fs, TypeVec.id.get, Function.comp_apply,
        id_eq] at this
      rw [this]
}

@[simp]
theorem transliterateMap_upMap_upMap {β γ δ}
    (g : γ → δ)
    (f : β → γ)
    (x : P (α ::: β))
    : transliterateMap g (upMap f x) = upMap (g ∘ f) x := 
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

@[simp]
theorem downMap_transliterateMap_downMap {β γ δ}
    (g : γ → δ)
    (f : β → γ)
    (x : P.uLift (α.uLift ::: β))
    : downMap g (transliterateMap f x) = downMap (g ∘ f) x := 
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

@[simp]
theorem downMap_upMap_map {β γ δ}
    (g : γ → δ)
    (f : β → γ)
    (x : P (α ::: β))
    : downMap g (upMap f x) = (TypeVec.id ::: g ∘ f) <$$> x :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

@[simp]
theorem upMap_downMap_transliterateMap {β γ δ}
    (g : γ → δ)
    (f : β → γ)
    (x : P.uLift (α.uLift ::: β))
    : upMap g (downMap f x) = transliterateMap (g ∘ f) x :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem downMap_map {α' : TypeVec _} {β γ β'}
    {f : α.uLift ⟹ α'.uLift}
    {f' : β → β'}
    {g : β' → γ}
    (x : P.uLift (α.uLift ::: β))
    : downMap g ((f ::: f') <$$> x) = downMap (g ∘ f') ((f ::: id) <$$> x) :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem downMap_map' {α' : TypeVec _} {β γ β'}
    {f : α.uLift ⟹ α'.uLift}
    {f' : β → β'}
    {g : β' → γ}
    (x : P.uLift (α.uLift ::: β))
    : downMap g ((f ::: f') <$$> x) = (f.uLift_arrow ::: id) <$$> downMap (g ∘ f') x :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem map_downMap {α' : TypeVec _} {β γ β'}
    {f : α ⟹ α'}
    {g : β → β'}
    {f' : β' → γ}
    (x : P.uLift (α.uLift ::: β))
    : (f ::: f') <$$> downMap g x = (f ::: id) <$$> downMap (f' ∘ g) x :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem map_downMap' {α' : TypeVec _} {β γ β'}
    {f : α ⟹ α'}
    {g : β → β'}
    {f' : β' → γ}
    (x : P.uLift (α.uLift ::: β))
    : (f ::: f') <$$> downMap g x = downMap (f' ∘ g) ((f.arrow_uLift ::: id) <$$> x) :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem map_upMap
    {α' : TypeVec _} {β γ β'}
    {f : α.uLift ⟹ α'}
    {f' : β' → γ}
    {g : β → β'}
    (x : P (α ::: β))
    : (f ::: f') <$$> upMap.{u, v} g x = (f ::: id) <$$> upMap (f' ∘ g) x :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem map_upMap'
    {α' : TypeVec _} {β γ β'}
    {f : α.uLift ⟹ α'.uLift}
    {f' : β' → γ}
    {g : β → β'}
    (x : P (α ::: β))
    : (f ::: f') <$$> upMap.{u, v} g x = upMap (f' ∘ g) ((f.uLift_arrow ::: id) <$$> x) :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem upMap_map {α' : TypeVec _} {β γ β'}
    {f : α ⟹ α'}
    {f' : β → β'}
    {g : β' → γ}
    (x : P (α ::: β))
    : upMap g ((f ::: f') <$$> x) = upMap (g ∘ f') ((f ::: id) <$$> x) :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

theorem upMap_map' {α' : TypeVec _} {β γ β'}
    {f : α ⟹ α'}
    {f' : β → β'}
    {g : β' → γ}
    (x : P (α ::: β))
    : upMap g ((f ::: f') <$$> x) = (f.arrow_uLift ::: id) <$$> upMap (g ∘ f') x :=
  Sigma.ext rfl <| heq_of_eq <| funext₂ fun
    | .fz, _ | .fs _, _ => rfl

@[inline]
def liftAppend {β} (x : P (α ::: β))
    : (uLift.{u, v} P) (TypeVec.uLift.{u, v} α ::: ULift.{u, max u v} (ULift β)) :=
  ((TypeVec.id ::: ULift.up) ⊚ .mpr TypeVec.uLift_append1_ULift_uLift)
    <$$> uLift_up x

@[simp]
theorem liftAppend_fst
    {β} {x : P (α ::: β)}
    : (liftAppend x).fst = .up x.fst := rfl

@[simp]
theorem lift_append_snd
    {β} {x : P (α ::: β)}
    : (liftAppend x).snd = ((TypeVec.id ::: .up) ⊚ .mpr TypeVec.uLift_append1_ULift_uLift) 
      ⊚ x.snd.arrow_uLift := rfl

end Sme

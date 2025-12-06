import Mathlib.Data.TypeVec

universe u v w x

namespace TypeVec
open scoped MvFunctor

variable {n : ℕ} {α α' β γ : TypeVec n} {f : α ⟹ β} {g : β ⟹ γ}

theorem comp_get {i : Fin2 n} : (g ⊚ f) i = g i ∘ f i := rfl

@[simp]
theorem append1_get_fz {α : TypeVec n} {β : Type u} : (α ::: β) .fz = β := rfl
@[simp]
theorem append1_get_fs {α : TypeVec n} {β : Type u} {v : Fin2 n} : (α ::: β) (.fs v) = α v := rfl

theorem splitFun_eq_appendFun {β β' : Type*} (f : α ⟹ α') (g : β → β')
    : appendFun f g = splitFun (α := append1 α β) (α' := append1 α' β') f g := rfl

theorem Arrow.comp_of_splitFun
    {α₁ : TypeVec.{u} n} {β₁ : TypeVec.{v} n}
    {α₂ : Type u} {β₂ : Type v}
    {β₃ : Type v}
    {f' : (α₁ ::: α₂) ⟹ (β₁ ::: β₂)}
    {f₁ : α₁ ⟹ β₁}
    {g₁ : α₂ → β₂}
    {x : β₂ → β₃}
    (h : f' = appendFun f₁ g₁)
    : appendFun f₁ (x ∘ g₁) = (appendFun id x) ⊚ f' :=
  h ▸ eq_of_drop_last_eq rfl rfl

theorem splitFun_comp_appendFun {α γ : TypeVec n} {β δ : Type*} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ γ) (f₁ : α ⟹ drop ε) (g₀ : last ε → δ) (g₁ : β → last ε) :
    splitFun f₀ g₀ ⊚ appendFun f₁ g₁  = appendFun (f₀ ⊚ f₁) (g₀ ∘ g₁) :=
  (splitFun_comp _ _ _ _).symm

section ULift

@[pp_with_univ]
def uLift (α : TypeVec.{u} n) : TypeVec.{max u v} n :=
  (_root_.ULift <| α ·)

@[simp]
theorem uLift_drop_comm
    {α : TypeVec.{u} n.succ}
    : α.uLift.drop = α.drop.uLift := rfl

@[simp]
theorem uLift_append1_ULift_uLift
    {β : Type u}
    {α : TypeVec.{u} n}
    : (TypeVec.uLift.{u, v} α ::: ULift.{v, u} β) = (α ::: β).uLift :=
  funext fun | .fz | .fs _ => rfl

@[pp_with_univ]
def Arrow.uLift_up {α : TypeVec.{u} n} : α ⟹ α.uLift := fun _ => ULift.up
@[pp_with_univ]
def Arrow.uLift_down {α : TypeVec.{u} n} : α.uLift ⟹ α :=
  fun _ => ULift.down
@[pp_with_univ]
def Arrow.transliterate.{y,z} {α : TypeVec.{u} n} : (uLift.{_,y} α) ⟹ (uLift.{_,z} α) :=
  uLift_up ⊚ uLift_down

def Arrow.uLift_arrow
    {α β : TypeVec n}
    (h : TypeVec.uLift.{u, v} α ⟹ TypeVec.uLift.{w, x} β)
    : α ⟹ β := uLift_down ⊚ h ⊚ uLift_up
def Arrow.arrow_uLift
    {α β : TypeVec n}
    (h : α ⟹ β)
    : TypeVec.uLift.{u, v} α ⟹ TypeVec.uLift.{w, x} β := 
  uLift_up ⊚ h ⊚ uLift_down

theorem Arrow.uLift_up_splitFun {α : TypeVec.{u} n.succ}
    : Arrow.uLift_up (α := α) = splitFun Arrow.uLift_up ULift.up :=
  funext fun | .fz | .fs _ => rfl

theorem Arrow.uLift_down_splitFun {α : TypeVec.{u} n.succ}
    : Arrow.uLift_down = splitFun (α := α.uLift) Arrow.uLift_down ULift.down := 
  funext fun | .fz | .fs _ => rfl

@[simp]
theorem Arrow.uLift_up_down {α : TypeVec.{u} n}
    : Arrow.uLift_up ⊚ (Arrow.uLift_down (α := α)) = id := rfl

@[simp]
theorem Arrow.uLift_down_up {α : TypeVec.{u} n}
    : Arrow.uLift_down ⊚ (Arrow.uLift_up (α := α)) = id := rfl

@[simp]
theorem Arrow.transliterate_idempotent
    : Arrow.transliterate ⊚ Arrow.transliterate = Arrow.transliterate (α := α) := rfl

theorem Arrow.uLift_arrow_splitFun
    {α : TypeVec n.succ}
    {β : TypeVec n.succ}
    (f : α.uLift.drop ⟹ β.uLift.drop)
    (g : α.uLift.last → β.uLift.last)
    : (splitFun f g).uLift_arrow = (splitFun f.uLift_arrow (ULift.down ∘ g ∘ .up)) :=
  funext fun | .fz | .fs _ => rfl

end ULift

@[simp]
theorem comp.get
  {A B C : TypeVec (n + 1)}
  {b : TypeVec.Arrow B C}
  {a : TypeVec.Arrow A B}
  {i}
  : (b ⊚ a) i = b i ∘ (a i) := rfl

@[simp]
theorem appendFun.get_fz {α β}
  {A B : TypeVec (n)}
  {a : TypeVec.Arrow A B}
  {v : α → β}
  : (a ::: v) .fz = v := rfl

@[simp]
theorem appendFun.get_fs {α β}
  {A B : TypeVec n}
  {a : TypeVec.Arrow A B}
  {v : α → β} {i}
  : (a ::: v) (.fs i) = a i := rfl

@[simp]
theorem uLift_down.get
    {α : TypeVec (n + 1)} {i}
    : Arrow.uLift_down (α := α) i = ULift.down := rfl

@[simp]
theorem uLift_up.get
    {α : TypeVec (n + 1)} {i}
    : Arrow.uLift_up (α := α) i = ULift.up := rfl

end TypeVec

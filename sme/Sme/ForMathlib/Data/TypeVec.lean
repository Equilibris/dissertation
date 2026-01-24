import Mathlib.Data.TypeVec
import Sme.ForMathlib.Data.ULift

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

namespace Arrow

@[pp_with_univ, inline]
def uLift_up {α : TypeVec.{u} n} : α ⟹ α.uLift := fun _ => ULift.up
@[pp_with_univ, inline]
def uLift_down {α : TypeVec.{u} n} : α.uLift ⟹ α :=
  fun _ => ULift.down
@[pp_with_univ, inline]
def transliterate.{y,z} {α : TypeVec.{u} n} : (uLift.{_,y} α) ⟹ (uLift.{_,z} α) :=
  uLift_up ⊚ uLift_down

def uLift_arrow
    {α β : TypeVec n}
    (h : TypeVec.uLift.{u, v} α ⟹ TypeVec.uLift.{w, x} β)
    : α ⟹ β := uLift_down ⊚ h ⊚ uLift_up
def arrow_uLift
    {α β : TypeVec n}
    (h : α ⟹ β)
    : TypeVec.uLift.{u, v} α ⟹ TypeVec.uLift.{w, x} β := 
  uLift_up ⊚ h ⊚ uLift_down

theorem arrow_uLift_appendFun {α' β'} {g : α' → β'}
    : arrow_uLift (appendFun f g)
    = .mp TypeVec.uLift_append1_ULift_uLift
    ⊚ appendFun (arrow_uLift f) (.up ∘ g ∘ ULift.down)
    ⊚ .mpr TypeVec.uLift_append1_ULift_uLift := funext fun
  | .fz | .fs _ => rfl

@[simp]
theorem arrow_uLift_id
    : arrow_uLift (TypeVec.id (α := α)) = TypeVec.id := rfl

@[simp]
theorem ulift_arrow_id
    : uLift_arrow (TypeVec.id (α := α.uLift)) = TypeVec.id := rfl

theorem uLift_up_splitFun {α : TypeVec.{u} n.succ}
    : .uLift_up (α := α) = splitFun uLift_up ULift.up :=
  funext fun | .fz | .fs _ => rfl

theorem uLift_down_splitFun {α : TypeVec.{u} n.succ}
    : uLift_down = splitFun (α := α.uLift) uLift_down ULift.down := 
  funext fun | .fz | .fs _ => rfl

@[simp]
theorem uLift_up_down {α : TypeVec.{u} n}
    : uLift_up ⊚ (uLift_down (α := α)) = id := rfl

@[simp]
theorem uLift_down_up {α : TypeVec.{u} n}
    : uLift_down ⊚ (uLift_up (α := α)) = id := rfl

@[simp]
theorem transliterate_idempotent
    : transliterate ⊚ transliterate = transliterate (α := α) := rfl

@[simp]
theorem transliterate_noop
    : transliterate (α := α) = TypeVec.id := rfl

theorem uLift_arrow_splitFun
    {α : TypeVec n.succ}
    {β : TypeVec n.succ}
    (f : α.uLift.drop ⟹ β.uLift.drop)
    (g : α.uLift.last → β.uLift.last)
    : (splitFun f g).uLift_arrow = (splitFun f.uLift_arrow (ULift.down ∘ g ∘ .up)) :=
  funext fun | .fz | .fs _ => rfl

end Arrow

theorem splitFun_comp'
    {α α' β : TypeVec (n + 1)}
    (f : α.drop ⟹ α'.drop)
    (g : α.last → α'.last)
    (h : α' ⟹ β)
    : h ⊚ TypeVec.splitFun f g = TypeVec.splitFun ((h ·.fs) ⊚ f) (h .fz ∘ g) :=
  funext fun | .fz | .fs _ => rfl

end ULift

@[simp]
theorem id.get {i} : TypeVec.id (α := α) i = _root_.id := rfl

@[simp]
theorem comp.get
  {A B C : TypeVec n}
  {b : TypeVec.Arrow B C}
  {a : TypeVec.Arrow A B}
  {i}
  : (b ⊚ a) i = b i ∘ (a i) := rfl

@[simp]
theorem appendFun.get_fz {α β}
  {A B : TypeVec n}
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
theorem splitFun.get_fz {α α' : TypeVec (n + 1)} {f : drop α ⟹ drop α'} {g : last α → last α'}
    : splitFun f g .fz = g := rfl

@[simp]
theorem splitFun.get_fs {α α' : TypeVec (n + 1)} {f : drop α ⟹ drop α'} {g : last α → last α'} {i}
    : splitFun f g (.fs i) = f i := rfl

@[simp]
theorem uLift_down.get
    {α : TypeVec (n + 1)} {i}
    : Arrow.uLift_down (α := α) i = ULift.down := rfl

@[simp]
theorem uLift_up.get
    {α : TypeVec (n + 1)} {i}
    : Arrow.uLift_up (α := α) i = ULift.up := rfl

@[simp]
theorem transliterate.get
    {α : TypeVec (n + 1)} {i}
    : Arrow.transliterate (α := α) i = ULift.transliterate := rfl

@[simp]
theorem mp.get {p : α = β} {i} : Arrow.mp p i = cast (funext_iff.mp p i) := rfl
@[simp]
theorem mpr.get {p : α = β} {i} : Arrow.mpr p i = cast (funext_iff.mp p.symm i) := rfl

@[simp]
theorem mp_rfl :  Arrow.mp  (Eq.refl α) = id := rfl
@[simp]
theorem mpr_rfl : Arrow.mpr (Eq.refl α) = id := rfl

@[simp]
theorem mpr_eq_mp {p : α = β} : .mpr p = Arrow.mp p.symm := rfl

@[simp]
theorem mp_mp {p : α = β} {q : β = γ} : .mp q ⊚ .mp p = .mp (p.trans q) := by
  funext i h
  simp

@[simp]
theorem mp_mpr {p : α = β} {q : γ = β} : .mpr q ⊚ .mp p = .mp (p.trans q.symm) := by
  simp

@[simp]
theorem mpr_mp {p : β = α} {q : β = γ} : .mp q ⊚ .mpr p = .mp (p.symm.trans q) := by
  simp

@[simp]
theorem mp_mpr' {p : α = β} : Arrow.mp p ⊚ Arrow.mpr p = TypeVec.id := by simp
@[simp]
theorem mpr_mp' {p : α = β} : Arrow.mpr p ⊚ Arrow.mp p = id := by simp

@[simp]
theorem repeat.get {X} : {n i : _} → TypeVec.repeat n X i = X
  | _, .fz => rfl
  | _, .fs i => repeat.get (i := i)

def repeat_out {X} (f : ∀ i, X → β i) : TypeVec.repeat n X ⟹ β :=
  fun i h => f i (repeat.get.mp h)

@[simp]
theorem last_eq {α : TypeVec (n + 1)} : TypeVec.last α = α .fz := rfl

attribute [simp] last_append1

@[simp]
theorem drop_append1_simp {α : TypeVec n} {β : Type _} : (α ::: β).drop = α := rfl

end TypeVec

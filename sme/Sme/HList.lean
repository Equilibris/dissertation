import Sme.ListMemT

universe u

inductive HList {A} (f : A → Type _) : List A → Type _
  | nil : HList f []
  | cons {hd tl} : f hd → HList f tl → HList f (hd :: tl)

namespace HList

def get {A t f} : {Γ : _} → List.MemT (A := A) t Γ → HList f Γ → f t
  | _ :: _, .hd, .cons h _ => h
  | _ :: _, .tl v, .cons _ tl => tl.get v

def map {A} {Γ : List A} {f g} (h : ∀ {v}, f v → g v) : HList f Γ → HList g Γ
  | .nil => .nil
  | .cons hd tl => .cons (h hd) <| tl.map h

@[simp]
theorem get_map {A} {Γ : List A} {f g : A → Type _} {a}
    {h : ∀ {v}, f v → g v}
    : {ls : HList f Γ} → (i : List.MemT a Γ) → (ls.map h).get i = h (ls.get i)
  | .cons _ _, .hd => rfl
  | .cons hd tl, .tl h' => by
    change get h' (map h tl) = h (tl.get h')
    exact get_map _

def map' {A B Γ} {Γm : A → B} {f g} (h : ∀ {v}, f v → g (Γm v)) : HList f Γ → HList g (Γ.map Γm)
  | .nil => .nil
  | .cons hd tl => .cons (h hd) <| tl.map' h

end HList


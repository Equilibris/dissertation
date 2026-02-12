namespace List

inductive MemT {A} : A → List A → Type
  | hd {a as} : MemT a (a :: as)
  | tl {bs a b} : MemT a bs → MemT a (b :: bs)

namespace MemT

def shift {A a} {l₁}
    : {l₂ : List A}
    → l₁.MemT a
    → (l₂ ++ l₁).MemT a
  | [], h => h
  | _ :: _, h => .tl (shift h)

def sandwitch_shift {A a l₁}
    : {l l₂ : List A}
    → (l ++ l₁).MemT a
    → (l ++ (l₂ ++ l₁)).MemT a
  | [], _, h => h.shift
  | _ :: _, _, .hd => .hd
  | _ :: _, _, .tl v => .tl v.sandwitch_shift

def remove
    {A v}
    : {l : List A}
    → l.MemT v
    → List A 
  | _ :: t, .hd => t
  | h :: _, .tl h' => h :: remove h'

def map {A B v} {f : A → B}
    : {l : List A}
    → l.MemT v
    → (l.map f).MemT (f v)
  | _ :: _, .hd => .hd
  | _ :: _, .tl h => .tl h.map

/- def mapo {f : A → B} -/
/-     : {l : List A} -/
/-     → l.MemT v -/
/-     → (l.map f).MemT (f v) -/

end List.MemT

inductive ListFunctor (α ρ : Type _) : Type _
  | nil
  | cons (hd : α) (tl : ρ)

inductive ListFunctor.Crystal
    {α : Type v} {base : Type (max u v)}
    : {n : Nat}
    → {m : Nat}
    → n.repeat (ListFunctor.{v, max u v} α) base
    → m.repeat (ListFunctor.{v, max u v} α) base → Prop where
  | base  :         @Crystal _ _ (0    ) (m + 1) b v
  | nilS  : n ≤ m → @Crystal _ _ (n + 1) (m + 1) .nil .nil
  | consS :         @Crystal _ _ (n    ) (m    ) t₁   t₂ →
                    @Crystal _ _ (n + 1) (m + 1) (.cons h₁ t₁) (.cons h₁ t₂)

structure CoList (α : Type _) where
  obj : (n : Nat) → n.repeat (ListFunctor α) Unit
  cryst : ∀ n, ListFunctor.Crystal (obj n) (obj n.succ)

namespace ListFunctor
def Crystal.order {base}
    : {n m : Nat} →
    {a : n.repeat (ListFunctor.{v, max u v} α) base} →
    {b : m.repeat (ListFunctor.{v, max u v} α) base} →
    Crystal a b → n ≤ m
  | 0, m+1, _, _, .base => by exact Nat.le_add_left 0 (m + 1)
  | _+1, _+1, .nil, .nil, .nilS h => Nat.add_le_add_right h _
  | _+1, _+1, .cons _ _, .cons _ _, .consS h => Nat.add_le_add_right (order h) 1

def Crystal.trans
    {base : Type _}
    : {n m k : Nat} →
    {a : n.repeat (ListFunctor.{v, max u v} α) base} →
    {b : m.repeat (ListFunctor.{v, max u v} α) base} →
    {c : k.repeat (ListFunctor.{v, max u v} α) base} →
    Crystal a b → Crystal b c → Crystal a c
  | _+1, _+1, _+1, .cons _ _, .cons _ _, .cons _ _, .consS hx, .consS hy =>
    .consS $ Crystal.trans hx hy
  | _+1, _+1, _+1, _, _, _, .nilS hx, .nilS hy =>
    .nilS $ Nat.le_trans hx hy
  | 0, _+1, _+1, _, _, _, .base, _ => .base

def Crystal.zero_up_gen
    {f : Nat → Nat}
    {obj : (n : Nat) → (f n).repeat (ListFunctor α) Unit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    : (n : Nat) → Crystal (obj 0) (obj n.succ)
  | n+1 => Crystal.zero_up_gen cryst n |>.trans $ cryst _
  | 0   => cryst 0

def Crystal.frwd_gen
    {f : Nat → Nat}
    {obj : (n : Nat) → (f n).repeat (ListFunctor α) Unit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    : (a b : Nat) → a < b → Crystal (obj a) (obj b)
  | a+1, b+1, h => frwd_gen
    (f := f ∘ Nat.succ)
    (obj := (obj ·.succ))
    (cryst ·.succ) a b
    (Nat.succ_lt_succ_iff.mp h)
  | 0,   _+1, _ => zero_up_gen cryst _

abbrev Crystal.frwd
    {obj : (n : Nat) → n.repeat (ListFunctor α) Unit}
    : (∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ)) →
    (a b : Nat) → a < b → Crystal (obj a) (obj b) := frwd_gen

namespace Crystal
def cons
    {obj : (n : Nat) → n.repeat (ListFunctor α) Unit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    (h : obj 1 = ListFunctor.cons hd PUnit.unit)
    : (x : Nat) → ∃ tl, obj x.succ = ListFunctor.cons hd tl
  | 0 => by
    have := cryst 1
    cases h' : obj 2 <;> simp_all [h', h]
  | n+1 => by
    have ⟨tl', h⟩ := Crystal.cons cryst h n
    have := cryst (n+1)
    cases h' : obj (n+2) <;> simp_all [h', h]
    <;> cases this
    exact ⟨_, rfl⟩

def nil
    {obj : (n : Nat) → n.repeat (ListFunctor α) Unit}
    (cryst : ∀ (n : Nat), ListFunctor.Crystal (obj n) (obj n.succ))
    (h : obj 1 = .nil)
    : (x : Nat) → obj x.succ = .nil
  | 0 => by
    have := cryst 1
    cases h' : obj 2 <;> simp_all [h', h]
  | n+1 => by
    have := cryst (n+1)
    cases h' : obj (n+2)
    <;> rw [h', nil cryst h n] at this
    clear h h'
    cases this
end Crystal

def Tight {α} {x : Nat} (v : x.succ.repeat (ListFunctor α) Empty) : Prop :=
  ¬∃ (y : x.repeat _ _), (Crystal y v)
end ListFunctor

structure List' (α : Type _) where
  bound : Nat
  content : bound.succ.repeat (ListFunctor α) Empty
  tightness : ListFunctor.Tight content

def List'.lift : {n : Nat} → n.repeat (ListFunctor α) Empty → List' α
  | _+1, .nil => ⟨0, .nil, Empty.elim ∘ Exists.choose⟩
  | n+1, .cons hd tl =>
    let ⟨n, v, tight⟩ := List'.lift tl
    ⟨n+1, .cons hd v, fun ⟨w, p⟩ => by cases p; exact tight ⟨_ , (by assumption)⟩⟩

def List'.cons : α → List' α → List' α
  | hd, ⟨n, tl, tight⟩ => ⟨
    n+1,
    .cons hd tl,
    fun ⟨w, p⟩ => match p with | .consS v => tight ⟨_ , v⟩⟩

def List'.nil : List' α := ⟨0, .nil, Empty.elim ∘ Exists.choose⟩

def List'.dest : List' α → ListFunctor α (List' α)
  | ⟨0, .nil, _⟩ | ⟨_+1, .nil, _⟩ => .nil
  | ⟨_+1, .cons hd tl, _⟩ => .cons hd $ List'.lift tl

structure CoList (α : Type _) where
  obj : (n : Nat) → n.repeat (ListFunctor α) Unit
  cryst : ∀ n, ListFunctor.Crystal (obj n) (obj n.succ)

-- This will in the end be the only efficent way to walk the graph sadly, and a bit pathalogically
def CoList.destN {n : Nat} (o : CoList α) : n.repeat (ListFunctor α) (CoList α) :=
  let ⟨obj, cryst⟩ := o
  let struct := obj n
  walker struct
where
  walker : {k : Nat} → k.repeat _ _ → k.repeat _ _
  | 0, _ => sorry
  | n+1, .nil => sorry
  | n+1, .cons _ _ => sorry

def CoList.dest (o : CoList α) : ListFunctor α (CoList α) :=
  let ⟨obj, cryst⟩ := o
  match h₁ : obj 1 with
  | .nil => .nil
  | .cons hd .unit =>
    .cons hd ⟨
      (fun x => match h₂ : obj x.succ with
      | .cons _ tl => tl
      | .nil => 
        have := ListFunctor.Crystal.frwd cryst 1 x.succ (by exact?)
        sorry
        /- ListFunctor.Crystal.cons cryst h₁ x -/
        /-   |> Exists.choose_spec  -/
        /-   |>.symm.trans h₂ -/
        /-   |> ListFunctor.noConfusion -/
      ),
      fun n => by
        dsimp
        split
        <;> rename_i heq₁
        case h_2 =>
          sorry
          /- exact ListFunctor.Crystal.cons cryst h₁ n -/
          /-   |> Exists.choose_spec -/
          /-   |>.symm.trans heq₁ -/
          /-   |> ListFunctor.noConfusion  -/
        have ⟨_, p⟩ := ListFunctor.Crystal.cons cryst h₁ n.succ 
        split
        <;> rename_i heq₂
        case h_2 =>
          exact ListFunctor.noConfusion $ p.symm.trans heq₂
        have := cryst n.succ
        rw [heq₁, heq₂] at this
        clear *-this
        exact match this with | .consS x => x
    ⟩

def CoList.corec.impl
    (f : ρ → ListFunctor α ρ) (content : ρ) 
    : (x : Nat) → x.repeat (ListFunctor α) Unit
  | 0 => .unit
  | _+1 => match f content with
    | .nil => .nil
    | .cons hd tl => .cons hd (impl f tl _)

-- TODO: Add the concept of an indexer type to make co-rec generation much faster (hopefully)
-- No, turns out this is a fundemental failure of progressive generation.
-- This can be fixed though, or at least made linear which should make scaling less insane.
-- To do this we need eacg approximation to become exponentially better than the last.
-- With this done the amortized cost will become 𝓞(n)

def CoList.corec.proof : ∀ (x : Nat), ListFunctor.Crystal (impl f v x) (impl f v x.succ)
  | 0 => .base
  | n+1 => by
    dsimp [corec.impl]
    match f v with
    | .nil      => exact .nilS  $ Nat.le_add_right n 1
    | .cons _ _ => exact .consS $ corec.proof n

def CoList.corec (f : ρ → ListFunctor α ρ) (v : ρ) : CoList α :=
  ⟨corec.impl f v, corec.proof⟩

abbrev TLs (l : List Type) : Type :=
  l.foldl Prod Unit

class SimpleCtorsND (t : Type _) where
  ctors : List $ (arg : Type _) × (arg → t)

class SimpleCasesND (t : Type) extends SimpleCtorsND t where
  cases {motive : t → Type} :
    ((ctors.map
      (fun ⟨args, ctor⟩ => (x : args) → motive (ctor x))).foldl Prod Unit) → ((x : t) → motive x)

def takeList (l : CoList α) : Nat → List α
  | 0 => []
  | n+1 =>
    match l.dest with
    | .nil => []
    | .cons hd tl => hd :: takeList tl n

#reduce takeList (CoList.corec (fun x => .cons x x.succ) 0) 99


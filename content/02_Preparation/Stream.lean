def StreamF (α ρ : Type _) := α × ρ

inductive StreamF.Crystal {α : Type} {base : Type} : {n : Nat} → {m : Nat}
    → n.repeat (StreamF α) base → m.repeat (StreamF α) base → Prop where
  | base  : @Crystal _ _ 0 (m + 1) b v
  | consS : @Crystal _ _ n m t₁ t₂ →
      @Crystal _ _ (n + 1) (m + 1) ⟨h₁, t₁⟩ ⟨h₁, t₂⟩

structure PA (α : Type _) : Type 0 where
  obj : (n : Nat) → n.repeat (StreamF α) Unit
  cryst : ∀ n, StreamF.Crystal (obj n) (obj (n + 1))

namespace PA
def corec.o (gen : ρ → StreamF α ρ) (v : ρ) : (n : Nat) → n.repeat (StreamF α) Unit
  | 0 => .unit | n + 1 => (gen v).map id (o gen · n)
def corec (gen : ρ → StreamF α ρ) (init : ρ) : PA α where
  obj := corec.o gen init
  cryst n := by
    induction n generalizing init
    · exact .base
    case succ n ih =>
      unfold corec.o
      rcases gen init with ⟨a, b⟩
      change StreamF.Crystal (n := n+1) (m := n+2) ⟨a, corec.o gen b n⟩ ⟨a, corec.o gen b (n + 1)⟩
      exact StreamF.Crystal.consS (h₁ := a) (ih b)

def dest (x : PA α) : StreamF α (PA α) := ⟨
  (x.obj 1).1,
  (x.obj ·.succ |>.snd),
  fun n => by
    have := x.cryst (n+1)
    dsimp
    generalize (x.obj (n + 1)) = a, (x.obj (n + 1 + 1)) = b at this;
    rcases a; rcases b; rcases this with (_|ih)
    exact ih
⟩
end PA

universe u v w

class Iter (M : Type u → Type _) where
  iter {A B : Type u} : (A → M (A ⊕ B)) → A → M B

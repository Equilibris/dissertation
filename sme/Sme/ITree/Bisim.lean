import CoinductivePredicates
import Sme.ITree.Defs

namespace Sme.ITree

universe u v

coinductive Bisim' (E : Type _ → Type _) (R : Type (u + 1))
    : Base E (ITree E R) R → Base E (ITree E R) R → Prop where
  | ret {r} : Bisim' E R (.ret r) (.ret r)
  | tau {t v} : Bisim' t.dest v.dest → Bisim' E R (.tau t) (.tau v)
  | vis {A e a b} : (∀ v : A, Bisim' (a v).dest (b v).dest) → Bisim' E R (.vis e a) (.vis e b)

namespace Bisim'

variable {E : Type u → Type u} {R : Type (u + 1)}

theorem refl {x} : Bisim' E R x x :=
  ⟨(· = ·), fun {x _} h => h ▸ (match x with
    | .tau _ => .tau rfl
    | .ret _ => .ret
    | .vis _ _ => .vis fun _ => rfl), rfl⟩

theorem symm {x y} : Bisim' E R x y → Bisim' E R y x :=
  fun ⟨r, ris, rxy⟩ =>
  ⟨
    (fun a b => r b a),
    (match ris · with
    | .ret => .ret
    | .tau v => .tau v
    | .vis v => .vis v) ,
    rxy
  ⟩

theorem trans {x y z} : Bisim' E R x y → Bisim' E R y z → Bisim' E R x z :=
  fun ⟨ra, rais, raxy⟩ ⟨rb, rbis, rbxy⟩ =>
  ⟨
    (∃ b, ra · b ∧ rb b ·),
    (fun ⟨_, ra, rb⟩ => match rais ra, rbis rb with
    | .ret, .ret => .ret
    | .tau ha, .tau hb => .tau ⟨_, ha, hb⟩
    | .vis ha, .vis hb => .vis fun _ => ⟨_, ha _, hb _⟩),
    ⟨_, raxy, rbxy⟩
  ⟩

inductive Invariant'
    (Z : PBase E !![R, HpLuM (PBase E) !![R]] → PBase E !![R, HpLuM (PBase E) !![R]] → Prop)
    : PBase E !![R, HpLuM (PBase E) !![R]] → PBase E !![R, HpLuM (PBase E) !![R]] → Prop
  | ret {v} : Invariant' _ ⟨.ret, v⟩ ⟨.ret, v⟩
  | tau {a b}
    : Z (a .fz PUnit.unit).dest (b .fz PUnit.unit).dest
    → Invariant' _ ⟨.tau, a⟩ ⟨.tau, b⟩
  | vis {A e a b}
    : (∀ z, Z (a .fz z).dest (b .fz z).dest )
    → Invariant' _ ⟨.vis A e, a⟩ ⟨.vis A e, b⟩

theorem toInvariant' {x y : PBase E !![R, HpLuM (PBase E) !![R]]} {r}
    (v : Invariant E R r (equivB.equiv x) (equivB.equiv y))
    : Invariant' (fun (a b) => r (equivB.equiv a) (equivB.equiv b)) x y := by
  change Invariant' _ (id x) (id y)
  have : _ = (id : PBase E !![R, HpLuM (PBase E) !![R]] → PBase _ _) := equivB.equiv.symm_comp_self
  rw [←this]; dsimp
  generalize equivB.equiv x = x, equivB.equiv y = y at *
  rcases v with (_|v|v)
  · exact .ret
  · refine .tau v
  · refine .vis fun z => v z.down

theorem bisim (a b : ITree E R) : Bisim' E R a.dest b.dest → a = b := by
  intro ⟨r, his, rab⟩
  apply HpLuM.bisim (fun (a b : ITree _ _) => r a.dest b.dest) rab
  clear *-his
  intro a b rab
  have v := toInvariant' <| his rab
  dsimp [dest, HpLuM.destE] at v
  generalize a.dest = x, b.dest = y at *
  clear *-v his
  rcases v with (_|v|v)
  · refine ⟨_, _, _, ⟨rfl, by rfl⟩, ⟨rfl, by rfl⟩, fun | .fs .fz, h => rfl | .fz, h => ?_⟩
    cases h
  · rename_i a b
    refine ⟨.tau, a, b, ?_⟩
    simp only [Nat.reduceAdd, heq_eq_eq, and_self, true_and]
    rintro (_|_|_|_) h
    · cases h
      exact v
    · cases h
  · rename_i a b
    refine ⟨.vis _ _, a, b, ?_⟩
    simp only [Nat.reduceAdd, heq_eq_eq, and_self, true_and]
    rintro (_|_|_|_) h
    · cases h
      apply v
    · cases h

end Bisim'

variable {E R}

def Bisim (a b : ITree E R) : Prop := Bisim' E R a.dest b.dest

namespace Bisim

variable {x y z : ITree E R}

theorem refl : Bisim x x := Bisim'.refl
theorem symm : Bisim x y → Bisim y x := Bisim'.symm
theorem trans : Bisim x y → Bisim y z → Bisim x z := Bisim'.trans

instance : Equivalence (Bisim : ITree E R → _ → _) where
  refl _ := refl
  symm := symm
  trans := trans

instance : Trans (Bisim : ITree E R → _ → _) Bisim Bisim := ⟨trans⟩

end Bisim

@[ext (iff := false)]
def bisim {a b : ITree E R} (h : Bisim a b) : a = b := Bisim'.bisim _ _ h

alias ext := bisim


end Sme.ITree


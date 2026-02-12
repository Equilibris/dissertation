import CoinductivePredicates
import Sme.ITree.Defs
import Sme.ITree.Combinators
import Sme.ITree.KTree
import Sme.ITree.WBisim.Step
import Sme.ITree.WBisim.Defs
import Sme.ITree.WBisim.Congr

namespace Sme

universe u v

variable {E : Type u → Type u} {A B C : Type _} {a b : ITree E A}

namespace ITree.WBisim

theorem bind_congr_arg
    {X} {k1 : KTree E A X}
    (h : a ≈ b)
    : bind a k1 ≈ bind b k1 := by
  change WBisim' _ _ _ _
  simp only [dest_bind]
  refine ⟨
    fun a b => ∃ c d , WBisim' E A c d
        ∧ bind_map k1 c = a
        ∧ bind_map k1 d = b,
    ?_,
    ⟨_,_, h, rfl, rfl⟩
  ⟩
  rintro a b (⟨x, y, h, rfl, rfl⟩)
  rcases Step.no_middle y with (rfl|⟨⟨_,⟨h'⟩⟩⟩|⟨⟨_,_,_,⟨h'⟩⟩⟩)
  · obtain rfl := h.eqSpin'
    exact .refl (.refl _) (.refl _)
  · have ⟨h⟩ := WBisim'.stepRet h' h.symm
    have h := h.toEStep.transp_bind_map k1
    have h' := h'.toEStep.transp_bind_map k1
    simp only [bind_map.ret] at h h'
    exact .refl h h'
  · have ⟨_, bs, ⟨h⟩⟩ := WBisim'.stepVis h' h.symm
    have h := h.toEStep.transp_bind_map k1
    have h' := h'.toEStep.transp_bind_map k1
    refine .vis h.toVisStep' h'.toVisStep' ?_
    intro v
    simp only [Function.comp_apply, dest_bind]
    refine ⟨_, _, bs v, rfl, rfl⟩

theorem bind_congr_cont
    {X} {k1 k2 : KTree E A X}
    (h : k1 ≈ₖ k2)
    : bind a k1 ≈ bind a k2 := by
  change WBisim' _ _ _ _
  simp only [dest_bind]
  refine ⟨
    fun a b => WBisim' E X a b ∨ ∃ k1 k2 v, k1 ≈ₖ k2
        ∧ bind_map k1 v = a
        ∧ bind_map k2 v = b,
    ?_,
    .inr ⟨_,_, _, h, rfl, rfl⟩
  ⟩
  rintro a b (h|⟨k1, k2, w, h, rfl, rfl⟩)
  · exact match h.unfold with
    | .refl ha hb => .refl ha hb
    | .ret ha hb => .ret ha hb
    | .vis ha hb h => .vis ha hb (.inl <| h ·)
  rcases Step.no_middle w with (rfl|⟨⟨w,⟨h'⟩⟩⟩|⟨⟨_,_,_,⟨h'⟩⟩⟩)
  · simp only [bind_map.tau, spin.bind_eq]
    exact .refl'
  all_goals
    apply WBisim'.Invariant.skip
      (h'.toEStep.transp_bind_map k1)
      (h'.toEStep.transp_bind_map k2)
  all_goals dsimp
  · specialize h w
    exact match h.unfold with
    | .refl ha hb => .refl ha hb
    | .ret ha hb => .ret ha hb
    | .vis ha hb h => .vis ha hb (.inl <| h ·)
  · refine .vis .vis .vis fun w => .inr ?_
    simp only [Function.comp_apply, dest_bind]
    exact ⟨_,_,_, h, rfl, rfl⟩

theorem bind_congr {X} {k1 k2 : KTree E A X}
    (h : a ≈ b)
    (h' : k1 ≈ₖ k2)
    : bind a k1 ≈ bind b k2 := calc
  bind a k1
    ≈ bind a k2 := bind_congr_cont h'
  _ ≈ bind b k2 := bind_congr_arg h

theorem iter_bisim {it : A → ITree E (A ⊕ B)} {v}
    : iter it v ≈ (it v).bind (Sum.elim (iter it) ITree.ret) := by
  rw [iter_eq]
  exact bind_congr_cont fun | .inr _ => .refl | .inl _ => tau

end Sme.ITree.WBisim


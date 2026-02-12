import CoinductivePredicates
import Sme.ITree.Defs
import Sme.ITree.Combinators
import Sme.ITree.KTree
import Sme.ITree.WBisim.Step
import Sme.ITree.WBisim.Defs
import Sme.ITree.WBisim.Congr
import Sme.ITree.WBisim.Monad

namespace Sme.ITree.WBisim

universe u v

variable {E : Type u → Type u} {A B C : Type _} {a b : ITree E A}

inductive IterTrace (it : A → ITree E (A ⊕ B)) : A → Prop
  | retR {v r} : Step (it v).dest (.ret <| .inr r) → IterTrace it v
  | loop {v l} : Step (it v).dest (.ret <| .inl l) → IterTrace it l → IterTrace it v
  | vis {v e a} : Step (it v).dest (.vis e a) → IterTrace it v

theorem it_trace' {it : A → ITree E (A ⊕ B)} {v w}
      (h : Step (bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret) (it v).dest) w)
    : IterTrace it v := by
  rcases Step.no_middle (it v).dest with (hSp|⟨(r|r), ⟨hR⟩⟩|⟨_,_,_,⟨hV⟩⟩)
  · simp only [hSp, bind_map.tau, spin.bind_eq] at h
    exact (Step.not_spin' h).elim
  · refine .loop hR ?_
    apply it_trace' (w := w)
    let := (hR.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret))
    simp [iter_eq] at this
    apply ((this.tau'.trans (.ofEq (by simp))).meet h)
  · exact .retR hR
  · refine .vis hV
termination_by h.depth
decreasing_by
· clear *- h hR
  simp only [bind_map.ret, Sum.elim_inl, Function.comp_apply, eq_mp_eq_cast, EStep.meet_depth,
    EStep.trans_depth, EStep.depth_tau', EStep.ofEq_depth, add_zero]
  refine Nat.sub_lt ?_ ?_
  · refine Nat.zero_lt_of_ne_zero ?_
    simp only [ne_eq, Step.depth0]
    rintro rfl
    have := (hR.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret))
    simp at this
    exact Step.tau_rhs (this.comp_step h)
  · clear *-
    simp

theorem it_trace {it : A → ITree E (A ⊕ B)} {v w}
    (h : Step (iter it v).dest w) : IterTrace it v := by
  simp only [iter_eq, dest_bind] at h
  apply it_trace' h

coinductive IterCotrace E A B (it : A → ITree E (A ⊕ B)) : A → Prop
  | spin {v} : it v = spin → IterCotrace E A B it v
  | step {v x} : Step (it v).dest (.ret <| .inl x) → IterCotrace x → IterCotrace E A B it v

theorem IterCotrace.unfold {it} : Is E A B it (IterCotrace E A B it) :=
  fun ⟨_, ris, rab⟩ =>
    match ris rab with
    | .spin h => .spin h
    | .step st h => .step st ⟨_, ris, h⟩

theorem IterCotrace_transfer
    {it it' : A → ITree E (A ⊕ B)}
    (h : it ≈ₖ it') {v}
    (hCt : IterCotrace E A B it v)
    : IterCotrace E A B it' v := by
  refine ⟨
    IterCotrace E A B it,
    ?_,
    hCt
  ⟩
  intro a h'
  rcases h'.unfold with (h'|⟨hv, h'⟩)
  · refine .spin ?_
    have := (h a)
    rw [h'] at this
    exact WBisim.spinEq_iff.mp this
  case step h' =>
    refine .step (Classical.choice <| (h a).stepRet hv) h'

theorem IterCotrace_transfer_iff
    {it it' : A → ITree E (A ⊕ B)}
    (h : it ≈ₖ it') {v}
    : IterCotrace E A B it v
    = IterCotrace E A B it' v := propext {
  mp := IterCotrace_transfer h
  mpr := IterCotrace_transfer (fun x => (h x).symm)
}

theorem IterCotrace_of_eqSpin {it v}
    (h' : iter it v = spin)
    : IterCotrace E A B it v := by
  refine ⟨
    (iter it · = spin),
    ?_,
    h',
  ⟩
  clear h' v
  rintro v h
  simp only [iter_eq, ITree.dest_eq_iff, dest_bind, spin.dest_eq] at h
  rcases Step.no_middle (it v).dest with (h|⟨v|v,⟨h'⟩⟩|⟨_,_,_, ⟨h'⟩⟩)
  · refine .spin ?_
    rwa [←spin.dest_eq, ←ITree.dest_eq_iff] at h
  · have h1 := (h'.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret))
    simp only [bind_map.ret, Sum.elim_inl, Function.comp_apply, dest_tau] at h1
    have h1 := h1.tau'
    refine .step h' ?_
    simp only [h] at h1
    have := h1.eqSpin
    rwa [←spin.dest_eq, ←ITree.dest_eq_iff] at this
  · have h1 := (h'.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret))
    simp only [bind_map.ret, Sum.elim_inr, dest_ret] at h1
    have h1 := h1.toRetStep'
    rw [h] at h1
    exact h1.not_spin'.elim
  · have h1 := (h'.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret)).toVisStep'
    simp [h] at h1
    exact h1.not_spin'.elim

theorem eqSpin_of_IterCotrace {it v}
    (h' : IterCotrace E A B it v)
    : iter it v = spin
    := by
  rcases h'.unfold with (h'|⟨hStep, hCont⟩)
  · simp [iter_eq, h']
  rw [iter_eq]
  refine bisim ⟨
    fun a b => (a = .tau spin ∧ b = .tau spin) ∨ (b = .tau spin
      ∧ ∃ v r, bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret) v = a
      ∧ Nonempty (Step v (Base.ret (Sum.inl r)))
      ∧ IterCotrace E A B it r)
      ,
    ?_,
    ?init,
  ⟩
  case init =>
    right
    simp only [spin.dest_eq, dest_bind, true_and]
    refine ⟨_, _, rfl, ⟨hStep⟩, hCont⟩
  clear *-
  rintro x _ (⟨rfl, rfl⟩|⟨rfl, v, r, rfl, ⟨hStep⟩, hCont⟩)
  · refine .tau <| .inl ?_
    simp
  rcases hStep with (hStep|_)
  · refine .tau ?_
    right
    simp only [spin.dest_eq, dest_bind, exists_and_left, true_and]
    refine ⟨_, rfl, _, ⟨hStep⟩, hCont⟩
  simp only [exists_and_left, bind_map.ret, Sum.elim_inl, Function.comp_apply, dest_tau]
  refine .tau ?_
  simp only [spin.dest_eq, iter_eq, dest_bind, true_and]
  rcases hCont.unfold with (h'|⟨hStep, hCont⟩)
  · left
    simp [h']
  right
  refine ⟨_, rfl, _, ⟨hStep⟩, hCont⟩

theorem eqSpin_iff_IterCotrace {it v}
    : (IterCotrace E A B it v)
    ↔ iter it v = spin where
  mp := eqSpin_of_IterCotrace
  mpr := IterCotrace_of_eqSpin

theorem it_spin
    {it it' : A → ITree E (A ⊕ B)}
    (h : it ≈ₖ it')
    {v : A}
    (h' : iter it v = spin)
    : iter it' v = spin := by
  rwa [← eqSpin_iff_IterCotrace, ←IterCotrace_transfer_iff h, eqSpin_iff_IterCotrace]

theorem iter_congr_cont {it it' : A → ITree E (A ⊕ B)} {v}
    (h : it ≈ₖ it')
    : iter it v ≈ iter it' v := by
  change WBisim' _ _ _ _
  simp only [iter_eq, dest_bind]
  refine ⟨
    fun a b => ∃ k1 k2 : ITree _ _, k1 ≈ k2
        ∧ (bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret) k1.dest) = a
        ∧ (bind_map (Sum.elim (ITree.tau ∘ iter it') ITree.ret) k2.dest) = b,
    ?_,
    ⟨_,_, h _, rfl, rfl⟩
  ⟩
  clear v
  rintro _ _ ⟨k1, k2, h, rfl, rfl⟩
  cases h.unfold' <;> clear h
  · simp
  case ret v h1 h2 =>
    refine .skip
      (h1.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret))
      (h2.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it') ITree.ret))
      ?_
    simp only [bind_map.ret]
    rcases v with (v|v)
    <;> simp only [Sum.elim_inl, Function.comp_apply, dest_tau, Sum.elim_inr, dest_ret]
    · refine .skip (.tau <| .refl _) (.tau <| .refl _) ?_
      clear h1 h2
      by_cases h' : ∃ z, Nonempty <| Step (iter it v).dest z
      · rcases h' with ⟨w, ⟨h'⟩⟩
        have := it_trace h'
        clear h'
        induction this
        case pos.retR v r h1 =>
          simp only [iter_eq, dest_bind]
          have h2 := Classical.choice <| (h v).stepRet h1
          have h1 := h1.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret)
          have h2 := h2.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it') ITree.ret)
          simp only [bind_map.ret, Sum.elim_inr, dest_ret] at h2 h1
          refine .ret h1.toRetStep' h2.toRetStep'
        case pos.loop v _ h1 _ hInd =>
          simp only [iter_eq, dest_bind]
          have h2 := Classical.choice <| (h v).stepRet h1
          have h1 := h1.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret)
          have h2 := h2.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it') ITree.ret)
          simp only [bind_map.ret, Sum.elim_inl, Function.comp_apply, dest_tau] at h2 h1
          refine .skip h1.tau' h2.tau' hInd
        case pos.vis v _ _ h1 =>
          simp only [iter_eq, dest_bind]
          have ⟨_, hB, ⟨h2⟩⟩ := (h v).stepVis h1
          have h1 := h1.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret)
          have h2 := h2.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it') ITree.ret)
          simp at h1 h2
          refine .vis h1.toVisStep' h2.toVisStep' ?_
          intro v
          simp only [Function.comp_apply, dest_bind]
          refine ⟨_,_, (hB v).symm, rfl, rfl⟩
      · simp only [not_exists, not_nonempty_iff, Step.no_step_eq] at h'
        simp only [←spin.dest_eq, ←ITree.dest_eq_iff] at h'
        rw [h']
        simp
        have := it_spin h h'
        simp [this]
    · exact .refl'
  case vis h h1 h2 =>
    refine .vis
      (h1.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it) ITree.ret)).toVisStep'
      (h2.toEStep.transp_bind_map (Sum.elim (ITree.tau ∘ iter it') ITree.ret)).toVisStep'
      ?_
    intro v
    simp only [Function.comp_apply, dest_bind]
    refine ⟨_, _, h v, rfl, rfl⟩

end Sme.ITree.WBisim


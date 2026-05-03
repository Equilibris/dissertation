import Mathlib.Logic.Small.Defs
import Mathlib.Data.Setoid.Basic

def Nat' := Quotient (Setoid.ker fun x : Nat ↦ x - 1)
@[simp] theorem mk_zero : (⟦0⟧ : Nat') = ⟦1⟧ := Quotient.sound rfl

def equivNat : Nat' ≃ Nat where
  toFun x := x.lift _ fun _ _ ↦ id
  invFun x := ⟦x + 1⟧
  left_inv x := x.inductionOn fun x ↦ x.recOn (by simp) (by simp)
  right_inv x := by simp

theorem Shrink.eq_of_equiv {α : Type u} {β : Type v} [Small.{w} α] [Small.{w} β]
    (equiv : α ≃ β) : Shrink.{w} α = Shrink.{w} β := by
  unfold Shrink
  have hu (x : Type w) : Nonempty (α ≃ x) = Nonempty (β ≃ x) :=
    propext ⟨Nonempty.map equiv.symm.trans, Nonempty.map equiv.trans⟩
  simp [hu]

def castNat : Shrink.{0} Nat' → Shrink.{0} Nat := cast (Shrink.eq_of_equiv equivNat)

theorem contradiction : False := by
  have : (equivShrink _).symm (castNat (equivShrink _ ⟦0⟧)) ≠
      (equivShrink _).symm (castNat (equivShrink _ ⟦1⟧)) := by native_decide
  simpa

/- 'contradiction' depends on axioms:
[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#print axioms contradiction

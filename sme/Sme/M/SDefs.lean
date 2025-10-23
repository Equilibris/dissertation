import CoinductivePredicates
import Mathlib.Data.Quot
import Mathlib.Tactic.DepRewrite
import Sme.ForMathlib.Data.PFunctor.Multivariate.M
import Mathlib.Control.Functor.Multivariate

namespace Sme

universe u v w x y z

variable {n : Nat}

#check MvPFunctor.M.dest

structure PreM (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) where
  corec ::
  {β : Type v}
  (gen : β → MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
  (g : β)

namespace PreM

variable {P : MvPFunctor.{u} (n + 1)} {α : TypeVec.{u} n} {β : Type v}

/- example (x : PreM.{u, v} P α) : True := -/
/-   have := MvFunctor.map (TypeVec.id ::: fun ⟨v⟩ => ULift.up (PreM.corec x.gen v)) <| x.gen x.g -/
/-   sorry -/

def lift (x : MvPFunctor.uLift.{u, v} P (TypeVec.uLift.{u, v} α ::: ULift.{u, v} β))
    : MvPFunctor.uLift.{u, max v w} P
        (TypeVec.uLift.{u, max v w} α ::: ULift.{max u w, v} β) where
  fst := .up x.fst.down
  snd := fun
    | .fz, .up v => .up (x.snd .fz (.up v)).down
    | .fs s, .up v => .up (x.snd (.fs s) (.up v)).down

def dest (x : PreM.{u, v} P α)
    : MvPFunctor.uLift P (TypeVec.uLift.{_, v + 1} α ::: PreM.{u, v} P α) :=
  MvFunctor.map (TypeVec.id ::: (PreM.corec x.gen ·.down))
    <| lift.{u, v, v+1}
    <| x.gen x.g

def IsBisim (R : PreM.{u, v} P α → PreM.{u, v} P α → Prop) : Prop :=
    ∀ s t, R s t →
      MvFunctor.LiftR (TypeVec.RelLast _ R) s.dest t.dest

def Bisim : PreM.{u, v} P α → PreM.{u, v} P α → Prop :=
  (∃ R, IsBisim R ∧ R · ·)

namespace Bisim

def refl (x : PreM.{u, v} P α) : Bisim x x :=
  ⟨Eq, fun | _, x, .refl _ => (MvPFunctor.liftR_iff _ _ _).mpr <| ⟨
      x.dest.fst, x.dest.snd, x.dest.snd, rfl, rfl,
      fun | .fz, _ | .fs _, _ => rfl
    ⟩, rfl⟩

variable {a b c : PreM.{u, v} P α}

def symm (h : Bisim a b) : Bisim b a :=
  have ⟨r, his, rab⟩ := h
  ⟨(fun a b => r b a),
    fun | x, y, rxy => (by
      have ⟨wa, ca, cb, ha, hb, h⟩ := (MvPFunctor.liftR_iff _ _ _).mp <| his _ _ rxy
      rw [ha, hb]
      apply (MvPFunctor.liftR_iff _ _ _).mpr
      use wa, cb, ca
      refine ⟨rfl, rfl, ?_⟩
      rintro (_|s) h'
      · exact h .fz h'
      · exact (h (.fs s) h').symm
      ), rab⟩

end PreM.Bisim

end Sme


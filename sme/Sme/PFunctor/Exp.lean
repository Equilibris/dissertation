import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite
import Mathlib.Order.Extension.Linear
import Sme.PFunctor.NatTrans
import Sme.PFunctor.Prod
import Sme.HEq


namespace PFunctor

open scoped MvFunctor

universe u v

variable {n : Nat}

def Exp (P Q : PFunctor.{u, u}) : PFunctor.{u, u} where
  A := (x : P.A → Q.A) × ∀ h, Q.B (x h) → PUnit ⊕ P.B h
  B x := (i : P.A) × { d : Q.B (x.1 i) // x.2 i d = .inl .unit }

def ev (P Q : PFunctor.{u, u}) α (v : P α) (exp : Exp P Q α) : Q α where
  fst := exp.fst.fst v.1
  snd z :=
    match h : exp.1.2 _ z with
    | .inl .unit => exp.snd ⟨v.1, z, h⟩
    | .inr x => v.snd x

end PFunctor

namespace MvPFunctor

open scoped MvFunctor

universe u

variable {n : Nat}

def Exp (P Q : MvPFunctor.{u} n) : MvPFunctor.{u} n where
  A := (x : P.A → Q.A) × ∀ h i, Q.B (x h) i → PUnit ⊕ P.B h i
  B x i := (j : P.A) × {d : Q.B (x.1 j) i // x.2 j i d = .inl .unit }

namespace Exp

def ev {P Q : MvPFunctor.{u} n} : NatTrans (prod (Exp P Q) P) Q where
  hd p := p.1.1 p.2
  child x i v :=
    match h : x.1.2 x.2 i v with
    | .inl .unit => .inl ⟨_, _, h⟩
    | .inr x => .inr x

def toMap {X Y Z : MvPFunctor.{u} n}
    (nt : NatTrans (prod X Y) Z)
    : NatTrans X (Exp Y Z) where
  hd x := ⟨
    fun y => nt.hd ⟨x, y⟩,
    fun h i v =>
      match nt.child _ _ v with
      | .inl v' => .inl .unit
      | .inr v => .inr v,
  ⟩
  child x i h :=
    match h' : nt.2 _ i h.2.1 with
    | .inl v => v
    | .inr v => False.elim <| by
      dsimp [Exp] at h
      have := h.2.2
      rw [h'] at this
      simp at this

def ofMap {X Y Z : MvPFunctor.{u} n}
    (nt : NatTrans X (Exp Y Z))
    : NatTrans (prod X Y) Z where
  hd x := (nt.hd x.1).1 x.2
  child x i h :=
    match h' : (nt.1 x.1).2 x.2 i h with
    | .inl .unit => .inl <| nt.2 x.1 i ⟨x.2, h, h'⟩
    | .inr v => .inr v

theorem ofMap_toMap
    {X Y Z : MvPFunctor n} {x : NatTrans (prod X Y) Z}
    : ofMap (toMap x) = x := by
  rcases x with ⟨hd, ch⟩
  refine NatTrans.ext_hd_child (by rfl) <| heq_of_eq ?_
  ext x i h
  change Z.B (hd x) i at h
  refine match h : ch x i h with | .inl _ => ?_ | .inr _ => ?_
  <;> simp only [toMap, NatTrans.hd_mkOfHdChild, NatTrans.child_mkOfHdChild, ofMap]
  <;> rw! (castMode := .all) [Prod.eta, h]
  <;> rfl

theorem toMap_ofMap {X Y Z : MvPFunctor n} {x : NatTrans X (Exp Y Z)}
    : toMap (ofMap x) = x := by
  rcases x with ⟨hd, ch⟩
  have : (toMap (ofMap { hd := hd, child := ch })).hd = hd := by
    dsimp
    funext v
    refine Sigma.ext rfl ?_
    simp only [ofMap, NatTrans.hd_mkOfHdChild, NatTrans.child_mkOfHdChild, toMap, heq_eq_eq]
    funext y i h
    ;   split        <;> rename_i heq
    <;> split at heq <;> rename_i heq'
    <;> rw [heq']
    any_goals cases heq
    rfl
  apply NatTrans.ext_hd_child
  · exact this
  · apply Function.hfunext rfl
    intro a _ rfl
    apply Function.hfunext rfl
    intro i _ rfl
    apply Function.hfunext (by rw [this])
    intro u v h
    simp only [ofMap, NatTrans.hd_mkOfHdChild, NatTrans.child_mkOfHdChild, toMap, heq_eq_eq]
    split
    case h_2 => grind
    rename_i heq
    split at heq
    <;> simp only [NatTrans.hd_mkOfHdChild, NatTrans.child_mkOfHdChild, reduceCtorEq] at heq
    rw [Sum.inl.injEq] at heq
    rw [←heq]
    congr!
    apply eq_of_heq
    apply HEq.trans ?_ h
    clear *-this
    rcases u with ⟨ua, uv, uc⟩
    dsimp only
    rw [←cast_eq_iff_heq (e := by rw [this])]
    rw [cast_sigma_snd (p := by rw [this])]
    refine Sigma.ext rfl <| heq_of_eq ?_
    ext
    grind

-- TODO: Prove this is natural


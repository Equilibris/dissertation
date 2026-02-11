import Sme.ListMemT
import Sme.HList
import Sme.ITree.Interp
import Sme.ITree.WBisim
import Sme.ITree.Events.Map
import Sme.ITree.Events.SubEvent

open Sme ITree

inductive Imp (N : Type) : Type
  -- arith
  | add (a b : Imp N)
  | mul (a b : Imp N)
  | sub (a b : Imp N)
  | constN (n : Int)
  -- variables
  | var    (v : N)
  | assign (k : N) (a : Imp N)
  -- IO
  | print (a : Imp N)
  | seq (a b : Imp N)
  -- control
  | ite (c t f : Imp N)
  | while (c b : Imp N)
deriving DecidableEq

inductive IOE : Type → Type
  | print : Int → IOE Unit

def sem {N} : Imp N → ITree (IOE ⊕, MapE N Int) Int
  -- arith
  | .add a b => do
    let a ← sem a
    let b ← sem b
    return a + b
  | .mul a b => do
    let a ← sem a
    let b ← sem b
    return a * b
  | .sub a b => do
    let a ← sem a
    let b ← sem b
    return a - b
  | .constN n => .ret n
  -- var
  | .var v => .trigger <| .inr <| .getD v 0
  | .assign k v => do
    let v ← sem v
    let _ ← .trigger <| .inr <| .insert k v
    return 0
  -- effects
  | .print v => do
    let v ← sem v
    let _ ← .trigger <| .inl <| .print v
    return 0
  | .seq a b => do
    let _ ← sem a
    sem b
  -- control
  | .while c b => .iter (fun _ => do
      let c ← sem c
      if c ≠ 0 then
        let _ ← sem b
        return .inl .unit
      else
        return .inr 0
    ) Unit.unit
  | .ite c t f => do
    let c ← sem c
    if c ≠ 0 then sem t
    else          sem f

def constProp {N} (inp : Imp N) : Imp N :=
  flat <| pass inp
where
  flat : Int ⊕ _ → _
    | .inl v => .constN v
    | .inr v => v
  pass : _ → Int ⊕ _
    | .add a b =>
      match pass a, pass b with
      | .inl a, .inl b => .inl (a + b)
      | .inr a, b => .inr <| .add a (flat b)
      | .inl a, .inr b => .inr <| .add (.constN a) b
    | .mul a b =>
      match pass a, pass b with
      | .inl a, .inl b => .inl (a * b)
      | .inr a, b => .inr <| .mul a (flat b)
      | .inl a, .inr b => .inr <| .mul (.constN a) b
    | .sub a b =>
      match pass a, pass b with
      | .inl a, .inl b => .inl (a - b)
      | .inr a, b => .inr <| .sub a (flat b)
      | .inl a, .inr b => .inr <| .sub (.constN a) b
    | .constN n => .inl n
    | .print v => .inr <| .print <| flat (pass v)
    | .var n => .inr <| .var n
    | .assign n v => .inr <| .assign n <| flat (pass v)
    | .seq a b =>
      match pass a, pass b with
      | .inl _, b => b
      | .inr a, .inl b => .inr <| .seq a (.constN b)
      | .inr a, .inr b => .inr <| .seq a b
    | .ite c t f =>
      match pass c, pass t, pass f with
      | .inl 0, _, f => f
      | .inl (.ofNat (_ + 1)), t, _ | .inl (.negSucc _), t, _ => t
      | .inr c, t, f => .inr <| .ite c (flat t) (flat f)
    | .while c b =>
      match pass c, pass b with
      | .inl 0, _ => .inl 0
      | .inl (.ofNat (_ + 1)), b | .inl (.negSucc _), b =>
        .inr <| .while (.constN 1) <| flat b
      | .inr c, b => .inr <| .while c <| flat b

open constProp in
theorem pass_inl_eq_wbisim {N} {a : Imp N} {v}
    (h : pass a = Sum.inl v)
    : sem a ≈ .ret v :=
  match a with
  | .constN _ => by
    obtain rfl := (Sum.inl.injEq _ _).mp h
    rfl
  | .add a b => by
    dsimp [pass] at h
    split at h
    · rename_i a' b' h₁ h₂
      obtain rfl := (Sum.inl.injEq _ _).mp h
      have h₁ := pass_inl_eq_wbisim h₁
      have h₂ := pass_inl_eq_wbisim h₂
      change ((sem a).bind fun a ↦ (sem b).bind fun b ↦ pure (a + b)) ≈ pure _
      trans (ITree.ret a').bind fun a ↦ (sem b).bind fun b ↦ pure (a + b)
      · exact WBisim.bind_congr_arg h₁
      rw [ret_bind]
      trans ((ITree.ret b').bind fun b ↦ pure (a' + b))
      · exact WBisim.bind_congr_arg h₂
      rw [ret_bind]
    · contradiction
    · contradiction
  | .sub a b => by
    dsimp [pass] at h
    split at h
    · rename_i a' b' h₁ h₂
      obtain rfl := (Sum.inl.injEq _ _).mp h
      have h₁ := pass_inl_eq_wbisim h₁
      have h₂ := pass_inl_eq_wbisim h₂
      change ((sem a).bind fun a ↦ (sem b).bind fun b ↦ pure (a - b)) ≈ pure _
      trans (ITree.ret a').bind fun a ↦ (sem b).bind fun b ↦ pure (a - b)
      · exact WBisim.bind_congr_arg h₁
      rw [ret_bind]
      trans ((ITree.ret b').bind fun b ↦ pure (a' - b))
      · exact WBisim.bind_congr_arg h₂
      rw [ret_bind]
    · contradiction
    · contradiction
  | .mul a b => by
    dsimp [pass] at h
    split at h
    · rename_i a' b' h₁ h₂
      obtain rfl := (Sum.inl.injEq _ _).mp h
      have h₁ := pass_inl_eq_wbisim h₁
      have h₂ := pass_inl_eq_wbisim h₂
      change ((sem a).bind fun a ↦ (sem b).bind fun b ↦ pure (a * b)) ≈ pure _
      trans (ITree.ret a').bind fun a ↦ (sem b).bind fun b ↦ pure (a * b)
      · exact WBisim.bind_congr_arg h₁
      rw [ret_bind]
      trans ((ITree.ret b').bind fun b ↦ pure (a' * b))
      · exact WBisim.bind_congr_arg h₂
      rw [ret_bind]
    · contradiction
    · contradiction
  | .var _
  | .assign _ _
  | .print _ => by
    simp [pass] at h
  | .seq a b => by
    dsimp [pass] at h
    split at h
    · rename_i a' h'
      have h₁ := pass_inl_eq_wbisim h'
      have h₂ := pass_inl_eq_wbisim h
      dsimp [sem, Bind.bind]
      change ((sem a).bind fun _ ↦ sem b) ≈ ret v
      trans ((ITree.ret a').bind fun _ ↦ sem b)
      · exact WBisim.bind_congr_arg h₁
      rw [ret_bind]
      exact h₂
    · contradiction
    · contradiction
  | .ite c t f => by
    dsimp [pass, sem, Bind.bind] at h ⊢
    split at h
    · rename_i h'
      have h₁ := pass_inl_eq_wbisim h'
      have h₂ := pass_inl_eq_wbisim h
      apply WBisim.trans (WBisim.bind_congr_arg h₁)
      rw [ret_bind]
      exact h₂
    · rename_i h'
      have h₁ := pass_inl_eq_wbisim h'
      have h₂ := pass_inl_eq_wbisim h
      apply WBisim.trans (WBisim.bind_congr_arg h₁)
      rw [ret_bind]
      exact h₂
    · rename_i h'
      have h₁ := pass_inl_eq_wbisim h'
      have h₂ := pass_inl_eq_wbisim h
      apply WBisim.trans (WBisim.bind_congr_arg h₁)
      rw [ret_bind]
      exact h₂
    · contradiction
  | .while c b => by
    dsimp [pass, sem, Bind.bind] at h ⊢
    split at h
    · rename_i h₁
      have h₁ := pass_inl_eq_wbisim h₁
      obtain rfl := (Sum.inl.injEq _ _).mp h
      rw [ITree.iter_eq, ITree.bind_assoc]
      apply WBisim.trans (((WBisim.bind_congr_arg h₁)))
      simp [pure]
      rfl
    · contradiction
    · contradiction
    · contradiction

open constProp in
mutual

theorem pass_inr_eq_wbisim {N} {a : Imp N} {v}
    (h : pass a = Sum.inr v)
    : sem a ≈ sem v :=
  match a with
  | .constN _ => by
    simp [pass] at h
  | .mul a b | .sub a b | .add a b => by
    dsimp [pass] at h
    split at h
    · contradiction
    · obtain rfl := (Sum.inr.injEq _ _).mp h
      rename_i a' h'
      have h := pass_inr_eq_wbisim h'
      dsimp [sem, Bind.bind]
      apply WBisim.bind_congr h
      intro a
      dsimp
      exact WBisim.bind_congr_arg constProp_safe
    · obtain rfl := (Sum.inr.injEq _ _).mp h
      rename_i h₁ h₂
      apply WBisim.trans <| WBisim.bind_congr_arg <| pass_inl_eq_wbisim h₁
      simp only [Bind.bind, ret_bind, sem]
      exact WBisim.bind_congr_arg <| pass_inr_eq_wbisim h₂
  | .var _ => by
    obtain rfl := (Sum.inr.injEq _ _).mp h
    rfl
  | .assign _ _
  | .print _ => by
    obtain rfl := (Sum.inr.injEq _ _).mp h
    dsimp [sem, Bind.bind]
    apply WBisim.bind_congr_arg
    exact constProp_safe
  | .seq a b => by
    dsimp [pass] at h
    split at h
    · rename_i h'
      apply WBisim.trans <| WBisim.bind_congr_arg <| pass_inl_eq_wbisim h'
      simp only [ret_bind]
      exact pass_inr_eq_wbisim h
    · obtain rfl := (Sum.inr.injEq _ _).mp h
      rename_i h₁ h₂
      dsimp [sem, Bind.bind]
      apply WBisim.bind_congr <| pass_inr_eq_wbisim h₁
      intro k
      exact pass_inl_eq_wbisim h₂
    · obtain rfl := (Sum.inr.injEq _ _).mp h
      rename_i h₁ h₂
      dsimp [sem, Bind.bind]
      apply WBisim.bind_congr <| pass_inr_eq_wbisim h₁
      intro k
      exact pass_inr_eq_wbisim h₂
  | .ite c t f => by
    dsimp [pass, sem, Bind.bind] at h ⊢
    split at h
    · rename_i h'
      apply WBisim.trans <| WBisim.bind_congr_arg <| pass_inl_eq_wbisim h'
      simp only [ite_not, ret_bind, ↓reduceIte]
      exact pass_inr_eq_wbisim h
    · rename_i h'
      apply WBisim.trans <| WBisim.bind_congr_arg <| pass_inl_eq_wbisim h'
      simp only [Nat.succ_eq_add_one, Int.ofNat_eq_natCast, Int.natCast_add, Int.cast_ofNat_Int,
        ite_not, ret_bind]
      split
      · omega
      · exact pass_inr_eq_wbisim h
    · rename_i h'
      apply WBisim.trans <| WBisim.bind_congr_arg <| pass_inl_eq_wbisim h'
      simp only [ite_not, ret_bind, Int.negSucc_ne_zero, ↓reduceIte]
      exact pass_inr_eq_wbisim h
    · obtain rfl := (Sum.inr.injEq _ _).mp h
      rename_i h'
      apply WBisim.bind_congr <| pass_inr_eq_wbisim h'
      intro k
      dsimp
      split
      · exact constProp_safe
      · exact constProp_safe
  | .while c b => by
    dsimp [pass, sem, Bind.bind] at h ⊢
    split at h
    any_goals contradiction
    all_goals obtain rfl := (Sum.inr.injEq _ _).mp h
    all_goals clear h
    all_goals simp only [ite_not, sem, ne_eq]
    all_goals apply WBisim.iter_congr_cont
    all_goals intro k
    all_goals simp only [Bind.bind, ret_bind, one_ne_zero, ↓reduceIte]
    all_goals rename_i heq
    case h_4 =>
      apply WBisim.bind_congr <| pass_inr_eq_wbisim heq
      intro c
      simp only
      split
      · rfl
      · exact WBisim.bind_congr_arg constProp_safe
    all_goals apply WBisim.trans <| WBisim.bind_congr_arg <| pass_inl_eq_wbisim heq
    all_goals simp only [Nat.succ_eq_add_one, Int.ofNat_eq_natCast, Int.natCast_add,
      Int.cast_ofNat_Int, ret_bind, ret_bind, Int.negSucc_ne_zero, ↓reduceIte]
    any_goals split
    any_goals omega
    all_goals exact WBisim.bind_congr_arg constProp_safe

theorem constProp_safe {N} {b : Imp N} : sem b ≈ sem (flat (pass b)) := by
  cases h : pass b
  · exact pass_inl_eq_wbisim h
  · exact pass_inr_eq_wbisim h
end


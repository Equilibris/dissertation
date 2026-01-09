import Sme.M.HpLuM

universe u v

variable (E : Type u → Type u)

namespace Sme.ITree

@[grind]
inductive Base (ρ R : Type _)
  | tau (r : ρ)
  | ret (t : R)
  | vis {A : Type u} (e : E A) (k : A → ρ)

namespace Base

variable {E}

@[grind]
def map {ρ ρ' R R'} (f : ρ → ρ') (g : R → R') : Base E ρ R → Base E ρ' R'
  | .tau t => .tau (f t)
  | .ret r => .ret (g r)
  | .vis e k => .vis e (f ∘ k)

@[simp, grind =]
theorem map_map {ρ ρ₁ ρ₂ R R₁ R₂}
    {f₁ : ρ → ρ₁} {f₂ : ρ₁ → ρ₂}
    {g₁ : R → R₁} {g₂ : R₁ → R₂}
    : {v : Base E _ _}
    → (v.map f₁ g₁).map f₂ g₂ = v.map (f₂ ∘ f₁) (g₂ ∘ g₁) 
  | .tau _ | .ret _ | .vis _ _ => rfl

@[simp, grind =]
theorem map_id {A B : Type _}
    : {v : Base E A B}
    → (v.map id id) = v
  | .tau _ | .ret _ | .vis _ _ => rfl

@[simp, grind =]
theorem map_id' {A B : Type _} : (map id id) = (id : Base E A B → _) := funext fun _ => map_id

theorem map_inj
      {ρ ρ' R R'}
      {f : ρ → ρ'}
      {g : R → R'}
      (finj : Function.Injective f)
      (ginj : Function.Injective g)
      : Function.Injective (Base.map (E := E) f g) := 
    fun
      | .ret _, .ret _, heq => by
        simp only [map, ret.injEq] at heq
        rw [ginj heq]
      | .vis _ _, .vis _ _, heq => by
        simp only [map, vis.injEq] at heq
        obtain ⟨rfl, rfl, h⟩ := heq
        simp only [vis.injEq, heq_eq_eq, true_and]
        funext i
        exact finj <| funext_iff.mp (eq_of_heq h) i
      | .tau _, .tau _, heq => by 
        simp only [map, tau.injEq] at heq
        rw [finj heq]

end Base

inductive PHBase : Type max v (u + 1)
  | tau
  | ret
  | vis (A : Type u) (e : E A)

def PBase : MvPFunctor.{max v (u + 1)} 2 where
  A := PHBase E
  B | .ret => !![PUnit, PEmpty]
    | .tau => !![PEmpty, PUnit]
    | .vis A _ => !![PEmpty, ULift.{max v (u + 1), u} A]

-- 2 does not work !?
instance equivB {E} : EquivP (1 + 1) (Base E) (PBase E) := ⟨{
  toFun
    | ⟨.tau, v⟩ => .tau (v .fz .unit)
    | ⟨.ret, v⟩ => .ret (v (.fs .fz) .unit)
    | ⟨.vis A e, v⟩ => .vis e (v .fz ∘ ULift.up)
  invFun
    | .tau v => ⟨.tau, fun | .fz, _ => v | .fs .fz, e => e.elim⟩
    | .ret v => ⟨.ret, fun | .fz, v => v.elim | .fs .fz, _ => v⟩
    | .vis (A := A) e k =>
      ⟨.vis A e, fun | .fz => k ∘ ULift.down | .fs .fz => PEmpty.elim⟩
  left_inv v := by
    rcases v with ⟨⟨_⟩|⟨_⟩|⟨A, e⟩, v⟩
    <;> refine Sigma.ext (by rfl) <| heq_of_eq ?_
    <;> simp only [Nat.reduceAdd]
    <;> funext i h
    <;> rcases i with (_|_|_|_)
    <;> rcases h with ⟨h⟩
    <;> rfl
  right_inv | .tau _ | .ret _ | .vis _ _ => rfl
}⟩

def equiv' {E R} {X : Type v} : PBase.{u, v} E !![ULift X, R] ≃ Base E R X :=
    Equiv.trans equivB.equiv <| {
      toFun := Base.map id ULift.down
      invFun := Base.map id ULift.up
      left_inv
        | .tau _ | .ret _ | .vis _ _ => rfl
      right_inv
        | .tau _ | .ret _ | .vis _ _ => rfl
    }

end ITree

-- I should be able to detach R and have it reside in v instead but this will require work
def ITree (R : Type v) : Type (max v (u + 1)) := HpLuM (ITree.PBase E) !![ULift R]

namespace ITree

def PFunc (A B : Type _ → Type _) := ∀ z, A z → B z

infix:100 " ↝ " => PFunc

variable {E} {R : Type _}

def dest : ITree E R → Base E (ITree E R) R := Base.map id ULift.down ∘ HpLuM.destE
def mk (v : Base E (ITree E R) R) : ITree E R :=
  HpLuM.mkE (show _ from Base.map id ULift.up v)

@[simp]
theorem _root_.ULift.up_down' {A : Type u} : (ULift.up ∘ ULift.down (α := A)) = id := 
  funext fun v => by simp
@[simp]
theorem _root_.ULift.down_up' {A : Type u} : (ULift.down (α := A) ∘ ULift.up) = id := 
  funext fun v => by simp

@[simp] theorem dest_mk {v : ITree E R} : mk (dest v) = v := by
  dsimp [mk, dest]
  rw [Base.map_map, ULift.up_down', Function.comp_id, Base.map_id, HpLuM.destE_mkE ]
@[simp] theorem mk_dest {v : Base E (ITree E R) R} : dest (mk v) = v := by 
  dsimp [mk, dest]
  rw [HpLuM.mkE_destE, Base.map_map, ULift.down_up', Function.comp_id, Base.map_id]

theorem dest.bij : Function.Bijective (dest : ITree E R → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    mk,
    fun _ => dest_mk,
    fun _ => mk_dest,
  ⟩
theorem dest.inj_eq {a b : ITree E R} : dest a = dest b ↔ a = b where
  mp v := dest.bij.injective v
  mpr v := v ▸ rfl

theorem mk.bij : Function.Bijective (mk : _ → ITree E R) :=
  Function.bijective_iff_has_inverse.mpr ⟨
    dest,
    fun _ => mk_dest,
    fun _ => dest_mk,
  ⟩
theorem mk.inj_eq {a b : Base E _ R} : mk a = mk b ↔ a = b where
  mp v := mk.bij.injective v
  mpr v := v ▸ rfl

def tau (t : ITree E R) : ITree E R := .mk <| .tau t
def ret (r : R) : ITree E R := .mk <| .ret r
def vis {A} (e : E A) (c : A → ITree E R) : ITree E R := .mk <| .vis e c

@[simp]
theorem dest_tau {t : ITree E R} : dest (tau t) = .tau t := by simp [mk, tau, dest]
@[simp]
theorem dest_ret {r : R} : dest (ret r) = .ret (E := E) r := by simp [mk, ret, dest]
@[simp]
theorem dest_vis {A} {e : E A} {c : A → ITree E R} : dest (vis e c) = .vis e c := by
  simp [mk, vis, dest]

def corec {β} (f : β → Base E β R) : β → ITree E R :=
  HpLuM.corec (match f · with
    | .ret r => ⟨.up .ret, fun | .fz, h => h.down.elim | .fs .fz, _ => .up (.up r)⟩
    | .tau t => ⟨.up .tau, fun | .fz, _ => .up t | .fs .fz, h => h.down.elim⟩
    | .vis e c => ⟨.up (.vis _ e), fun | .fz, v => .up (c v.down.down) | .fs .fz, h => h.down.elim⟩
  )

@[simp]
theorem dest_corec {β g} (gen : β → Base E β R)
    : (corec gen g).dest = (gen g).map (corec gen) id := by
  dsimp [corec, dest, HpLuM.destE]
  rw [HpLuM.dest_corec, ←corec]
  cases gen g
  · rfl
  · rfl
  · simp only [Base.map, EquivP.equiv, Nat.reduceAdd, TypeVec.append1_get_fs, Vec.append1.get_fz,
      TypeVec.append1_get_fz, MvPFunctor.uLift_down, MvPFunctor.map_fst, MvPFunctor.map_snd,
      Equiv.coe_fn_mk, Function.id_comp, Base.vis.injEq, heq_eq_eq, true_and]
    funext i
    rfl

/- theorem corec_roll {α β v} -/
/-     (f : α → β) -/
/-     (g : β → Base E α R) -/
/-     : corec (g ∘ f) v = corec (.map f id ∘ g) (f v) := by -/
/-   sorry -/

@[ext 100]
theorem dest_eq {a b : ITree E R} (h : dest a = dest b) : a = b :=
  HpLuM.ext_destE <| Base.map_inj
    Function.injective_id
    ULift.down_injective
    h

@[ext 100]
theorem mk_eq {a b : Base E _ R} (h : mk a = mk b) : a = b :=
  Base.map_inj
    Function.injective_id
    ULift.up_injective
    <| HpLuM.ext_mkE h

/- def dtcorec -/
/-     {β : Type v} -/
/-     (gen : β → -/
/-       DeepThunk -/
/-         (MvPFunctor.uLift.{u + 1, v} (PBase E)) -/
/-         (TypeVec.uLift.{u + 1, v} !![R] ::: ULift.{u + 1, v} β)) -/
/-     : β → ITree E R := -/
/-   DeepThunk.corec gen -/

end Sme.ITree


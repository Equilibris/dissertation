import Sme.PFunctor.Prj
import Sme.M.HpLuM
import Sme.M.Futu
import Sme.Vec

universe u v

namespace Sme

def NTMonad α := M DTSum !![α]

namespace NTMonad

variable {α β γ}

def dest : NTMonad α → α ⊕ NTMonad α := DTSum.equiv' ∘ M.dest

def corec {β} (f : β → α ⊕ β) : β → NTMonad α :=
  M.corec (fun v =>
    match f v with
    | .inl v => ⟨.up <| .up .true,  fun | .fs .fz, _ => .up v | .fz, h => h.down.elim⟩
    | .inr v => ⟨.up <| .up .false, fun | .fz, _ => .up v | .fs .fz, h => h.down.elim⟩
  )

@[simp]
theorem dest_corec {g} (gen : β → α ⊕ β)
    : (corec gen g).dest = (gen g).map id (corec gen) := by
  dsimp [corec, dest]
  rw [M.dest_corec, ←corec]
  simp only [Nat.reduceAdd]
  cases gen g
  <;> simp [Sum.map_inl, Sum.map_inr, id_eq]
  <;> rfl

def tau : NTMonad α → NTMonad α :=
  .mk ∘ DTSum.equiv'.symm ∘ .inr

def ret : α → NTMonad α :=
  .mk ∘ DTSum.equiv'.symm ∘ .inl

@[simp]
theorem dest_tau {v : NTMonad α} : dest (tau v) = .inr v := by
  simp [dest, tau]
  rfl

@[simp]
theorem dest_ret {v : α} : dest (ret v) = .inl v := by
  simp [dest, ret]
  rfl

@[elab_as_elim]
def cases {motive : NTMonad α → Sort _}
    (hTau : ∀ v, motive (tau v)) (hRet : ∀ v, motive (ret v))
    (v : _) : motive v := by
  cases v using M.mk_cases; next v =>
  cases v using DTSum.cases
  case hCont =>
    apply hTau
  case hRecall v =>
    apply hRet

@[ext 1100]
theorem ext {a b : NTMonad α}
    (h : a.dest = b.dest)
    : a = b := by
  cases a using cases
  <;> cases b using cases
  <;> simp only [dest_ret, dest_tau, Sum.inl.injEq, reduceCtorEq, Sum.inr.injEq] at h
  <;> subst h
  <;> rfl

theorem bisim (R : NTMonad α → NTMonad α → Prop)
    {a b : NTMonad α}
    (h' : R a b)
    (h : ∀ a b, R a b → Sum.LiftRel Eq R a.dest b.dest)
    : a = b :=
  M.bisim_map R h' fun s t r => by
    cases s using M.mk_cases; next s =>
    cases t using M.mk_cases; next t =>
    simp only [Nat.reduceAdd, MvPFunctor.map_fst, M.mk_dest]
    specialize h _ _ r
    simp only [dest, Function.comp_apply, M.mk_dest] at h
    cases s using DTSum.cases
    <;> cases t using DTSum.cases
    <;> simp only [DTSum.equiv', DTSum.recall, DTSum.cont, Equiv.coe_fn_mk,
      Sum.liftRel_inl_inl, Sum.not_liftRel_inl_inr, Sum.liftRel_inr_inr,
      Sum.not_liftRel_inr_inl, DTSum.recall.f, DTSum.cont.f ] at h
    · simp only [DTSum.map_cont, TypeVec.appendFun.get_fz, Function.const_apply, exists_true_left]
      intro v
      rw! (castMode := .all) [M.mk_dest]
      generalize_proofs p1 p2
      generalize p1 ▸ v = v
      rw! (castMode := .all) [M.mk_dest]
      exact h
    · subst h
      simp only [cast_eq, DTSum.map_recall, TypeVec.appendFun.get_fs, TypeVec.id.get,
        Vec.append1.get_fz, id_eq, exists_const]
      intro z
      rw! (castMode := .all) [M.mk_dest]
      generalize_proofs p1 p2
      generalize p1 ▸ z = x
      cases x

def map (f : α → β) (v : NTMonad α) : NTMonad β :=
  corec go v
where go v := match v.dest with
  | .inl v => .inl <| f v
  | .inr v => .inr <| v

@[simp]
theorem dest_map (f : α → β) (v : NTMonad α) : dest (map f v) = v.dest.map f (map f) := by
  cases v using cases <;> simp [map, map.go]

theorem id_map (v : NTMonad α) : map id v = v := by
  apply bisim (fun a b => map id b = a) rfl
  rintro a v rfl
  cases v using cases
  · simp
  · simp

theorem comp_map (g : α → β) (h : β → γ) (x : NTMonad α) : map (h ∘ g) x = map h (map g x) := by
  apply bisim (fun a b => ∃ x, map (h ∘ g) x = a ∧ map h (map g x) = b) ⟨_, rfl, rfl⟩
  rintro _ _ ⟨x, rfl, rfl⟩
  cases x using cases
  · simp only [dest_map, dest_tau, Sum.map_inr, Sum.liftRel_inr_inr]
    exact ⟨_, rfl, rfl⟩
  · simp

instance : Functor NTMonad where map := map
instance : LawfulFunctor NTMonad where
  id_map := id_map
  comp_map := comp_map
  map_const := rfl

def bind (v : NTMonad α) (f : α → NTMonad β) : NTMonad β :=
  corec go <| Sum.inl (β := NTMonad β) v
where go
  | .inl v => match v.dest with
    | .inl v => .inr <| .inr <| f v
    | .inr v => .inr <| .inl v
  | .inr v => match v.dest with
    | .inl v => .inl v
    | .inr v => .inr <| .inr v

@[simp]
theorem dest_bind (v : NTMonad α) (f : α → NTMonad β) : dest (bind v f)
    = v.dest.elim (.inr ∘ f) (.inr <| bind · f) := by
  cases v using cases 
  · simp only [bind, dest_corec, bind.go, dest_tau, Sum.map_inr, Sum.elim_inr]
  simp only [bind, dest_corec, bind.go, dest_ret, Sum.map_inr, Sum.elim_inl, Function.comp_apply,
    Sum.inr.injEq]
  apply bisim (fun a b => a = corec (bind.go f) (.inr b) ) rfl
  rintro _ b rfl
  cases b using cases <;> simp [bind.go]

instance : Monad NTMonad where
  pure := ret
  bind := bind

@[simp]
theorem ret_bind
    (x : β)
    (f : β → NTMonad α)
    : (ret x).bind f = f x := by
  ext
  simp []
  sorry

@[simp]
theorem pure_bind
    (f : β → γ)
    (g : NTMonad β)
    : g.bind (pure ∘ f) = map f g := by
  apply bisim (fun a b => a = b ∨ ∃ g, a = g.bind (pure ∘ f) ∧ b = map f g) <| .inr ⟨_, rfl, rfl⟩
  rintro a _ (rfl|⟨g, rfl, rfl⟩)
  · cases a using cases <;> simp
  simp only [dest_bind, dest_map]
  cases g using cases
  · simp only [dest_tau, Sum.elim_inr, Sum.map_inr, Sum.liftRel_inr_inr]
    exact .inr ⟨_, rfl, rfl⟩
  · 
    simp only [dest_ret, Sum.elim_inl, Function.comp_apply, Sum.map_inl]
    sorry
  simp only [dest_bind, dest_map]
  cases g using cases
  case hRecall => simp [pure]
  simp only [dest_cont, Sum.elim_inr, Function.comp_apply, Sum.map_inr, Sum.liftRel_inr_inr,
    transliterateMap_fst, cast_eq, transliterateMap_map, Function.const_comp, Function.comp_const,
    id_eq, exists_const]
  simp only [transliterateMap, ULift.transliterate_down, TypeVec.comp.get, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, TypeVec.transliterate.get, Function.comp_apply]
  exact fun _ => ⟨_, rfl, rfl⟩

theorem bind_assoc
    {γ δ ε}
    (x : Free P α γ)
    (f : γ → Free P α δ)
    (g : δ → Free P α ε)
    : (x.bind f).bind g = x.bind fun a ↦ (f a).bind g := by
  apply bisim
    (fun a b => a = b ∨ ∃ x : Free _ _ _, a = (x.bind f).bind g ∧ b = x.bind fun a ↦ (f a).bind g) 
    <| .inr ⟨_, rfl, rfl⟩
  rintro s _ (rfl|⟨x, rfl, rfl⟩)
  · cases s using cases <;> simp
  simp only [dest_bind]
  cases x using cases
  · simp only [dest_cont, Sum.elim_inr, Function.comp_apply, transliterateMap_comp,
      Sum.liftRel_inr_inr, transliterateMap_fst, cast_eq, transliterateMap_map, Function.const_comp,
      Function.comp_const, id_eq, exists_const]
    exact fun _ => .inr ⟨_, rfl, rfl⟩
  case hRecall v =>
    simp only [dest_recall, Sum.elim_inl, Function.comp_apply, dest_bind]
    cases f v using cases
    next => simp
    next v =>
    simp only [dest_recall, Sum.elim_inl, Function.comp_apply]
    cases g v using cases
    · simp
    simp


end Sme.NTMonad


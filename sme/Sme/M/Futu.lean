import Sme.M.DT.DTSum
import Sme.M.HpLuM
import Sme.HEq

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {n : Nat} {β : Type _} {α : TypeVec.{u} n}

def Free (P : MvPFunctor.{u} (n + 1)) (α : TypeVec.{u} n) (β : Type v) : Type max u v :=
  HpLuM (comp DTSum !![const _ (ULift β), P.uLift]) α.uLift

variable {P : MvPFunctor (n + 1)}

namespace Free

def recall (v : β) : Free P α β :=
  .mk <| comp.mk <| DTSum.recall <| const.mk _ <| .up v

def cont (v : P.uLift (α.uLift ::: Free P α β)) : Free P α β :=
  .mk <| comp.mk <| DTSum.cont v

def cont' (v : P (α ::: Free P α β)) : Free P α β :=
  cont <| upMap id v

@[elab_as_elim]
def cases {motive : Free P α β → Sort _}
    (hCont : ∀ v, motive (cont v)) (hRecall : ∀ v, motive (recall v))
    (v : _) : motive v := by
  cases v using HpLuM.mk_cases; next v =>
  cases v using comp.mk_cases; next v =>
  cases v using DTSum.cases
  case hCont =>
    apply hCont
  case hRecall v =>
    cases v using const.mk_cases; next v =>
    rcases v with ⟨v⟩
    apply hRecall

@[elab_as_elim]
def cases' {motive : Free P α β → Sort _}
    (hCont : ∀ v, motive (cont' v)) (hRecall : ∀ v, motive (recall v))
    (v : Free P α β) : motive v := by
  cases v using cases
  case hCont v =>
    dsimp [cont'] at hCont
    specialize hCont (downMap id v)
    simpa [TypeVec.appendFun_id_id] using hCont
  · apply hRecall

def dest (v : Free P α β) : β ⊕ P.uLift (α.uLift ::: Free P α β) :=
  DTSum.cases .inr (.inl ∘ ULift.down ∘ const.get)
    (comp.get (HpLuM.dest v))

def dest' : Free P α β → β ⊕ P (α ::: Free P α β) :=
  Sum.map id (downMap id) ∘ dest

@[simp]
theorem dest_recall {v} : dest (.recall v : Free P α β) = .inl v := by
  simp [recall, dest]
@[simp]
theorem dest_cont {v} : dest (.cont v : Free P α β) = .inr v := by
  simp [cont, dest]

@[simp]
theorem dest'_recall {v} : dest' (.recall v : Free P α β) = .inl v := by
  simp [dest']
@[simp]
theorem dest'_cont' {v} : dest' (.cont' v : Free P α β) = .inr v := by
  simp [dest', cont', TypeVec.appendFun_id_id]

@[simp]
theorem dest_cont' {v} : dest (.cont' v : Free P α β) = .inr (upMap id v) := by
  simp [cont']

@[simp]
theorem dest'_cont {v} : dest' (.cont v : Free P α β) = .inr (downMap id v) := by
  simp [dest']

@[ext 1100]
theorem ext {a b : Free P α β}
    (h : a.dest = b.dest)
    : a = b := by
  cases a using HpLuM.mk_cases; next a =>
  cases b using HpLuM.mk_cases; next b =>
  cases a using comp.mk_cases; next a =>
  cases b using comp.mk_cases; next b =>
  cases a using DTSum.cases
  <;> cases b using DTSum.cases
  <;> simp only [dest, Vec.append1.get_fz, Vec.append1.get_fs, HpLuM.mk_dest, comp.get_mk,
    DTSum.cases_cont, Sum.inr.injEq, DTSum.cases_recall, Function.comp_apply, reduceCtorEq,
    Sum.inl.injEq, ULift.down_inj] at h
  · subst h; rfl
  next a b =>
    cases a using const.mk_cases; next a =>
    cases b using const.mk_cases; next b =>
    simp only [const.get_mk] at h
    subst h
    rfl

@[ext 1200]
theorem ext' {a b : Free P α β}
    (h : a.dest' = b.dest')
    : a = b := by
  cases a using cases'
  <;> cases b using cases'
  <;> simp only [dest'_cont', dest'_recall, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
  <;> subst h
  <;> rfl

def squash : NatIso (uLift.{max u v, w} (uLift.{u, v} P)) (uLift.{u, max v w} P) where
  equiv := {
    toFun x := ⟨.up x.1.down.down, fun i h => x.2 i (.up <| .up h.down)⟩
    invFun x := ⟨.up <| .up x.1.down, fun i h => x.2 i (.up h.down.down)⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  nat' _ := rfl

def equiv : NatIso (uLift.{max u v, w} (DTSum.comp !![const _ (ULift.{u, v} β), uLift.{u, v} P]))
    (DTSum.comp !![const _ (ULift.{max u w} β), uLift.{u, max v w} P]) :=
  .trans comp.uLift
    <| comp.niLift DTSum.lift fun
      | .fz => squash
      | .fs .fz => .trans const.ulift <| const.transp <| {
        toFun := ULift.transliterate ∘ ULift.down
        invFun := ULift.up ∘ ULift.transliterate
      }

def corec {γ : Type w}
    (gen : γ → β ⊕ P.uLift (α.uLift ::: ULift.{u} γ))
    (v : γ)
    : Free P α β :=
  HpLuM.corec body v
where body := (
  equiv.symm <|
    match gen · with
    | .inl v =>
      comp.mk <| DTSum.recall <| const.mk _ <| .up v
    | .inr v =>
      comp.mk
        <| DTSum.cont
        <| ((.uLift_up ⊚ TypeVec.Arrow.transliterate.{_,max v w,_}) ::: id) <$$>
          transliterate v
  )

def corec' {γ : Type _}
    (gen : γ → β ⊕ P (α ::: γ))
    (v : γ)
    : Free P α β :=
  HpLuM.corec' body v
where body := (
  match gen · with
  | .inl v =>
    comp.mk <| DTSum.recall <| const.mk _ <| .up v
  | .inr v => comp.mk
    (DTSum.cont (((TypeVec.id ::: ULift.down) ⊚
      .mpr TypeVec.uLift_append1_ULift_uLift) <$$> uLift_up.{u, u} v))
  )

@[simp]
theorem dest_corec {γ : Type w}
    (gen : γ → β ⊕ P.uLift (α.uLift ::: ULift.{u} γ))
    (v : γ)
    : (corec gen v).dest = (gen v).map id (transliterateMap (corec gen ∘ ULift.down)) := by
  dsimp [corec, dest]
  rw [HpLuM.dest_corec]
  dsimp [corec.body]
  rcases gen v with (v|v)
  <;> dsimp
  · rfl
  · rw [NatIso.symm_nat, comp.map_mk, DTSum.map_cont]
    rw [MvFunctor.map_map, TypeVec.comp_assoc, TypeVec.appendFun_comp']
    dsimp [equiv]
    rw [NatIso.trans_symm, NatIso.trans, comp.niLift_symm_symm]
    dsimp
    rw [DTSum.lift.symm.nat', DTSum.map_cont]
    simp only [Vec.append1.get_fz, comp.uLift_mk, comp.get_mk]
    rw [DTSum.lift.symm.nat, DTSum.map_cont, DTSum.uLift_down_lift_symm]
    dsimp
    congr
    refine Sigma.ext rfl <| heq_of_eq <| funext₂ fun i h => ?_
    rcases i with (_|_)
    <;> rfl

@[simp]
theorem dest'_corec' {γ : Type _}
    (gen : γ → β ⊕ P (α ::: γ))
    (v : γ)
    : (corec' gen v).dest' = (gen v).map id (MvFunctor.map (TypeVec.id ::: corec' gen)) := by
  simp only [dest', corec', Function.comp_apply, dest, Vec.append1.get_fz, Vec.append1.get_fs,
    HpLuM.dest_corec', corec'.body, TypeVec.mpr_eq_mp]
  rcases gen v with (_|_)
  · simp [comp.map_mk]
  · simp only [comp.map_mk, DTSum.map_cont, Vec.append1.get_fz, map_map, comp.get_mk,
    DTSum.cases_cont, Sum.map_inr, Sum.inr.injEq]
    change  uLift_down.{u, u}
      ((.mp _ ⊚ ((_ ::: _) ⊚ (_ ::: _) ⊚ (_ ::: _)) ⊚ .mp _) <$$>
        uLift_up.{u, u} _) = _
    simp only [TypeVec.appendFun_comp', TypeVec.comp_id]
    change uLift_down.{u, u} ((.mp _ ⊚ ((TypeVec.id.arrow_uLift ::: (ULift.up ∘ _ ∘ ULift.down ))) ⊚ .mpr TypeVec.uLift_append1_ULift_uLift) <$$> uLift_up.{u, u} _) = _
    rw [←TypeVec.Arrow.arrow_uLift_appendFun, ←uLift_down_nat]
    simp
    rfl

@[simp]
theorem dest'_corec {γ : Type w}
    (gen : γ → β ⊕ P.uLift (α.uLift ::: ULift.{u} γ))
    (v : γ)
    : (corec gen v).dest'
    = Sum.map id
      (uLift_down
      ∘ MvFunctor.map
        (.mp TypeVec.uLift_append1_ULift_uLift
        ⊚ (TypeVec.id ::: ULift.up ∘ corec gen ∘ ULift.down))) (gen v) := by
  dsimp [dest']
  simp only [dest_corec, Sum.map_map, Function.comp_id]
  congr
  funext x
  simp
  rfl

theorem bisim {a b : Free P α β}
    (R : Free P α β → Free P α β → Prop) (x : R a b)
    (h :
      ∀ s t, R s t →
        Sum.LiftRel Eq (fun s t =>
          ∃ (x :
            (TypeVec.id ::: Function.const _ PUnit.unit) <$$> s =
            (TypeVec.id ::: Function.const _ PUnit.unit) <$$> t),
            ∀ v, R (s.snd Fin2.fz v) (t.snd Fin2.fz (cast (by
              rw [show s.fst = t.fst from (Sigma.ext_iff.mp x).1]) v)))
        s.dest t.dest)
    : a = b := by
  apply HpLuM.bisim_map R x
  intro s t r
  change Free _ _ _ at s t
  have := h s t r
  cases s using HpLuM.mk_cases; next s =>
  cases t using HpLuM.mk_cases; next t =>
  cases s using comp.mk_cases; next s =>
  cases t using comp.mk_cases; next t =>
  cases s using DTSum.cases
  <;> cases t using DTSum.cases
  <;> simp only [dest, Vec.append1.get_fz, Vec.append1.get_fs, HpLuM.mk_dest, comp.get_mk,
    DTSum.cases_recall, Function.comp_apply, Sum.liftRel_inl_inl, ULift.down_inj,
    DTSum.cases_cont, Sum.not_liftRel_inl_inr, Sum.not_liftRel_inr_inl, Sum.liftRel_inr_inr] at this
  <;> rename_i s t
  <;> dsimp at s t
  · simp only [map_fst, HpLuM.mk_dest, comp.map_mk, DTSum.map_cont, Vec.append1.get_fz]
    rcases this with ⟨hc, hr⟩
    use hc ▸ rfl
    intro v
    conv =>
      rhs
      rewrite! (castMode := .all) [HpLuM.mk_dest]
      skip
    rw! (castMode := .all) [HpLuM.mk_dest]
    rewrite! (castMode := .all) [HpLuM.mk_dest]
    dsimp
    rw [DTSum.comp_cont_fst, DTSum.comp_cont_fst]
    clear *-hr
    generalize_proofs p1 p2
    generalize p1 ▸ v = x
    have := hr (DTSum.dive x)
    generalize_proofs p3 at this
    suffices h : (DTSum.dive (cast p2 x)) = (cast p3 (DTSum.dive x)) from h ▸ this
    clear this
    rcases x with ⟨(_|_|_|_), (_|_), h⟩
    have : s.fst = t.fst := (Sigma.ext_iff.mp hc).1
    rw [cast_sigma_snd (p := by
      ext (_|_|_|_)
      any_goals rfl
      simp
      congr
      ext (_|_)
      congr)]
    rw [cast_sigma_snd (p := by
      ext (_|_|_|_)
      simp
      congr)]
    simp [DTSum.dive]
  · cases s using const.mk_cases; next s =>
    cases t using const.mk_cases
    subst this
    simp only [const.get_mk, map_fst, cast_eq, HpLuM.mk_dest, exists_const]
    intro v
    simp only [HpLuM.mk_dest] at v
    rcases v with ⟨(_|_|_|_),(_|_),(_|_)⟩

theorem bisim' {a b : Free P α β}
    (R : Free P α β → Free P α β → Prop) (x : R a b)
    (h :
      ∀ s t, R s t →
        Sum.LiftRel Eq (fun s t =>
          ∃ (x :
            (TypeVec.id ::: Function.const _ PUnit.unit) <$$> s =
            (TypeVec.id ::: Function.const _ PUnit.unit) <$$> t),
            ∀ v, R (s.snd Fin2.fz v) (t.snd Fin2.fz (cast (by
              rw [show s.fst = t.fst from (Sigma.ext_iff.mp x).1]) v)))
        s.dest' t.dest')
    : a = b := by
  apply bisim R x
  intro s t r
  change Free _ _ _ at s t
  have := h s t r
  cases s using cases'
  <;> cases t using cases'
  <;> simp only [dest'_recall, dest'_cont', Sum.liftRel_inl_inl, Sum.liftRel_inr_inr, 
      Sum.not_liftRel_inl_inr, Sum.not_liftRel_inr_inl] at this
  · simp only [dest_cont', Sum.liftRel_inr_inr]
    rw! [map_upMap, TypeVec.appendFun_id_id]
    rw! [map_upMap, TypeVec.appendFun_id_id]
    simp only [Function.comp_id, MvFunctor.id_map, upMap_eq_upMap]
    rcases this with ⟨h, h'⟩
    use h
    intro ⟨v⟩
    simp only [upMap, Function.id_comp, TypeVec.mpr_eq_mp, map_fst, uLift_up_fst, map_snd,
      uLift_up_snd, TypeVec.comp.get, TypeVec.append1_get_fz, TypeVec.appendFun.get_fz,
      TypeVec.mp.get, TypeVec.arrow_uLift.get, Function.comp_apply, cast_eq]
    specialize h' v
    generalize_proofs p1 at h'
    rw [cast_ulift_up _ p1]
    exact h'
  · subst this
    simp

def bind {γ : Type w} (a : Free P α β) (f : β → Free P α γ) : Free P α γ :=
  .corec body (.inl a : Free P α β ⊕ Free P α γ)
where body
  | .inl v =>
    match v.dest with
    | .inl x =>
      match (f x).dest with
      | .inl x => .inl x
      | .inr v => .inr <| transliterateMap (ULift.up ∘ .inr) v
    | .inr v => .inr <| transliterateMap (ULift.up ∘ .inl) v
  | .inr v =>
    match v.dest with
    | .inl x => .inl x
    | .inr v => .inr <| transliterateMap (ULift.up ∘ .inr) v

@[simp]
theorem bind_inr {γ} (f : β → Free P α γ)
    : (corec (bind.body f) ∘ ULift.down) ∘ ULift.up ∘ Sum.inr = id := by 
  funext x
  simp only [Function.comp_apply, id_eq]
  apply bisim (fun a b => corec (bind.body f) (Sum.inr b) = a) rfl
  rintro _ t rfl
  simp
  cases t using cases
  <;> simp [bind.body, MvPFunctor.map_map, TypeVec.appendFun_comp']

@[simp]
theorem dest_bind {γ : Type w} (a : Free P α β) (f : β → Free P α γ)
    : (bind a f).dest = (dest a).elim (dest ∘ f) (.inr ∘ transliterateMap (bind · f)) := by
  simp only [bind, dest_corec]
  cases a using cases
  · simp [bind.body]
    rfl
  next v =>
    simp only [bind.body, dest_recall, Sum.elim_inl, Function.comp_apply]
    cases f v using cases
    <;> simp [dest_cont, Sum.map_inr, transliterateMap_comp, bind_inr, transliterateMap_eq_map,
      dest_recall, Sum.map_inl, id_eq, TypeVec.appendFun_id_id]

def map {γ : Type w} (f : β → γ) (a : Free P α β) : Free P α γ :=
  .corec (Sum.map f (transliterateMap ULift.up) ∘ dest ) a

@[simp]
theorem dest_map {γ : Type w} (f : β → γ) (a : Free P α β)
    : (map f a).dest = (dest a).map f (transliterateMap (map f)) := by
  simp [map]
  cases a using cases
  <;> simp; rfl

@[simp]
theorem dest'_map {γ} (f : β → γ) (a : Free P α β)
    : (map f a).dest' = (dest' a).map f (MvFunctor.map (TypeVec.id ::: map f)) := by
  simp only [map, dest'_corec, Function.comp_apply, Sum.map_map, Function.id_comp]
  cases a using cases'
  case hRecall => simp
  simp only [dest_cont', Sum.map_inr, Function.comp_apply, transliterateMap_eq_map, dest'_cont',
    Sum.inr.injEq]
  simp [←MvPFunctor.map_map, eq_downMap, map_upMap, TypeVec.appendFun_id_id]
  rfl

@[simp]
theorem map_recall {γ} (f : β → γ) x
    : map f (recall (P := P) (α := α) x)
    = recall (f x) := by
  refine ext ?_
  simp

@[simp]
theorem map_cont {γ} (f : β → γ) x
    : map f (cont (P := P) (α := α) x)
    = cont (transliterateMap (map f) x) := by
  refine ext ?_
  simp

@[simp]
theorem map_cont' {γ} (f : β → γ) x
    : map f (cont' (P := P) (α := α) x)
    = cont' ((TypeVec.id ::: map f) <$$> x) := by
  refine ext' ?_
  simp

instance : Functor (Free P α) where
  map := map

instance : Monad (Free P α) where
  pure := recall
  bind := bind

@[simp]
theorem id_map (a : Free P α β) : map id a = a := by
  apply bisim (fun a b => map id b = a) rfl
  rintro _ x rfl
  rw [dest_map]
  cases x using cases
  case hCont =>
    simp [MvPFunctor.map_map, TypeVec.appendFun_comp']
  case hRecall =>
    simp

theorem comp_map {δ γ}
    (g : β → γ) (h : γ → δ)
    (x : Free P α β)
    : map (h ∘ g) x = (map h (map g x)) := by
  apply bisim (fun a b => ∃ x, map (h ∘ g) x = a ∧ map h (map g x) = b) ⟨_, rfl, rfl⟩
  rintro _ _ ⟨x, rfl, rfl⟩
  simp only [dest_map, Sum.map_map]
  cases x using cases
  <;> simp only [dest_recall, Sum.map_inl, Function.comp_apply, Sum.liftRel_inl_inl,
      transliterateMap_map, dest_cont, Sum.map_inr, Function.comp_apply, transliterateMap_comp,
      Sum.liftRel_inr_inr, transliterateMap_fst, cast_eq, transliterateMap_map,
      Function.const_comp, Function.comp_const, id_eq, exists_const]
  simp only [transliterateMap, ULift.transliterate_down, TypeVec.comp.get, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, TypeVec.transliterate.get, Function.comp_apply]
  exact fun _ => ⟨_, rfl, rfl⟩

instance : LawfulFunctor (Free P α) where
  id_map := id_map
  comp_map := comp_map
  map_const := rfl

@[simp]
theorem recall_bind
    {γ}
    (x : β)
    (f : β → Free P α γ)
    : (recall x).bind f = f x := by
  ext
  simp

@[simp]
theorem pure_bind
    {β γ}
    (f : β → γ)
    (g : Free P α β)
    : g.bind (pure ∘ f) = map f g := by
  apply bisim (fun a b => ∃ g, a = g.bind (pure ∘ f) ∧ b = map f g) ⟨_, rfl, rfl⟩
  rintro _ _ ⟨g, rfl, rfl⟩
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

instance : LawfulMonad (Free P α) where
  pure_bind := recall_bind
  bind_pure_comp := pure_bind
  bind_assoc := bind_assoc
  bind_map {β γ} f x := rfl
  pure_seq f x := by
    change bind (recall _) _ = _
    simp
  seqRight_eq x y := by
    change bind _ (Function.const _ _) = bind (map _ _) _
    rw [←pure_bind, bind_assoc]
    congr; funext h
    simp [pure]
  seqLeft_eq x y := by
    change (x.bind fun a ↦ y.bind fun x ↦ recall a) = bind (map _ _) _
    rw [←pure_bind, bind_assoc]
    congr; funext h
    simp only [pure, Function.comp_apply, recall_bind]
    change bind _ (pure ∘ _) = _
    rw [pure_bind]
    rfl

def inject β : HpLuM P α → Free P α β :=
  .corec <| .inr ∘ upMap .up ∘ HpLuM.dest

@[simp]
theorem dest_inject {x : HpLuM P α} : (inject β x).dest = .inr (upMap (inject _) x.dest) := by
  simp [inject, transliterateMap_upMap_upMap]
  rfl

@[simp]
theorem dest'_inject {x : HpLuM P α}
    : (inject β x).dest'
    = .inr ((TypeVec.id ::: inject _) <$$>x.dest) := by
  simp [dest']

@[simp]
theorem map_inject {β γ}
    {x : HpLuM P α}
    (f : β → γ)
    : map f (inject β x) = inject γ x := by
  apply bisim (fun a b => ∃ x, a = map f (inject β x) ∧ b = inject γ x) ⟨_, rfl, rfl⟩
  rintro _ _ ⟨x, rfl, rfl⟩
  simp only [dest_map, dest_inject, Sum.map_inr, transliterateMap_upMap_upMap, Sum.liftRel_inr_inr,
    cast_eq, map_upMap, Function.const_comp, Function.comp_const, id_eq, exists_const]
  intro v
  refine ⟨_, rfl, rfl⟩

theorem inject_injective : Function.Injective (inject (P := P) (α := α) β) := by
  intro x y h
  apply HpLuM.bisim_map (inject β · = inject β ·) h
  intro s t h
  have := Free.ext_iff.mp h
  cases s using HpLuM.mk_cases; next s =>
  cases t using HpLuM.mk_cases; next t =>
  rcases s with ⟨sh, st⟩
  rcases t with ⟨th, tt⟩
  simp only [dest_inject, HpLuM.mk_dest, Sum.inr.injEq] at this ⊢
  obtain rfl : _ := (ULift.up.injEq _ _).mp (Sigma.ext_iff.mp this).1
  have := eq_of_heq (Sigma.ext_iff.mp this).2
  dsimp at this
  rw! [HpLuM.mk_dest, HpLuM.mk_dest]
  simp only [map_mk, cast_eq, exists_prop]
  refine ⟨?_, ?_⟩
  · refine Sigma.ext rfl <| heq_of_eq <| funext₂ fun | .fz, h | .fs i, h => ?_
    · rfl
    · exact (ULift.up.injEq _ _).mp <| funext_iff.mp (funext_iff.mp this i.fs) <| .up h
  intro v
  exact funext_iff.mp (funext_iff.mp this .fz) (.up v)

def flatten : Free P α (HpLuM P α) → HpLuM P α :=
  .corec' body ∘ Sum.inl (β := HpLuM P α)
where
  body := Sum.elim
    (Sum.elim
      handle
      (MvFunctor.map (TypeVec.id ::: .inl))
    ∘ dest')
    handle
  handle := MvFunctor.map (TypeVec.id ::: .inr) ∘ HpLuM.dest

theorem flatten_inr : HpLuM.corec' (P := P) (α := α) flatten.body ∘ Sum.inr = id := by 
  funext x
  dsimp
  apply HpLuM.bisim_map (fun a b => .corec' flatten.body (.inr b) = a) rfl
  rintro _ x rfl
  simp only [map_fst, HpLuM.dest_corec']
  refine ⟨?a, ?_⟩
  · simp [flatten.body, flatten.handle, MvPFunctor.map_map, TypeVec.appendFun_comp']
  intro v
  rw! (castMode := .all) [HpLuM.dest_corec']
  simp
  rfl

@[simp]
theorem dest_flatten {x : Free P α _}
    : (flatten x).dest
    = x.dest'.elim HpLuM.dest (MvFunctor.map (TypeVec.id ::: flatten))
    := by
  change HpLuM.dest (.corec' _ _) = _
  simp only [HpLuM.dest_corec']
  cases x using cases'
  · simp [flatten.body, MvPFunctor.map_map, TypeVec.appendFun_comp']
    rfl
  · simp only [flatten.body, flatten.handle, Sum.elim_inl, Function.comp_apply, dest'_recall,
      map_map, TypeVec.appendFun_comp', TypeVec.comp_id]
    change (TypeVec.id ::: HpLuM.corec' flatten.body ∘ _) <$$> _ = _
    rw [flatten_inr, TypeVec.appendFun_id_id, MvFunctor.id_map]

@[simp]
theorem flatten_recall {x}
    : flatten (recall (P := P) (α := α) x) = x := by
  ext
  simp

@[simp]
theorem flatten_cont {x}
    : flatten (cont (P := P) (α := α) x) = .mk (downMap flatten x) := by
  ext
  simp [map_downMap, TypeVec.appendFun_id_id]

@[simp]
theorem flatten_cont' {x}
    : flatten (cont' (P := P) (α := α) x) = .mk ((TypeVec.id ::: flatten) <$$> x) := by
  ext
  simp

@[simp]
theorem flatten_inject {x : HpLuM P α} : flatten (inject _ x) = x := by
  apply HpLuM.bisim_map (fun a b => flatten (inject _ b) = a) rfl
  rintro _ x rfl
  refine ⟨?_, ?_⟩
  · simp [dest_flatten, MvPFunctor.map_map, TypeVec.appendFun_comp']
  intro v
  rw! (castMode := .all) [dest_flatten, dest'_inject ]
  simp

def futu
    (f : β → P.uLift (α.uLift ::: Free P α β))
    (seed : β)
    : HpLuM P α :=
  .corec (transliterateMap (.up ∘ Sum.elim f id ∘ dest)) (f seed)

def futu'
    (f : β → P (α ::: Free P α β))
    (seed : β)
    : HpLuM P α :=
  .corec' (MvFunctor.map (TypeVec.id ::: Sum.elim f id ∘ dest')) (f seed)

theorem futu_flatten_mk
    (f : β → P.uLift (α.uLift ::: Free P α β))
    (seed : β)
    : futu f seed = .mk (downMap (flatten ∘ map (futu f)) (f seed)) := by
  dsimp [futu]
  apply HpLuM.bisim_map (fun a b =>
    a = b ∨
    ∃ x,
      a = HpLuM.corec (transliterateMap (ULift.up ∘ Sum.elim f id ∘ dest)) x ∧
      b = HpLuM.mk (downMap.{u, u_1} (flatten ∘ map (futu f)) x)
    ) <| .inr ⟨_, rfl, rfl⟩
  rintro _ _ (rfl|⟨x, rfl, rfl⟩)
  · simp
  refine ⟨?_, ?_⟩
  · simp only [HpLuM.dest_corec, uLift_down_nat, TypeVec.Arrow.arrow_uLift_appendFun,
      TypeVec.Arrow.arrow_uLift_id, Function.const_comp, Function.comp_const, TypeVec.mpr_eq_mp,
      map_map, TypeVec.comp_assoc, TypeVec.mp_mp_assoc, TypeVec.mp_rfl, TypeVec.id_comp,
      TypeVec.appendFun_comp', TypeVec.comp_id, HpLuM.mk_dest, map_downMap, TypeVec.appendFun_id_id,
      MvFunctor.id_map]
    rw [←MvPFunctor.map_map, transliterateMap_map, TypeVec.appendFun_id_id, MvFunctor.id_map]
    simp [eq_downMap]
  intro v
  rw! (castMode := .all) [HpLuM.dest_corec, HpLuM.mk_dest]
  dsimp [transliterateMap , downMap]
  rw [eqRec_eq_cast]
  generalize_proofs p1 p2 p3
  generalize x.snd Fin2.fz (ULift.up (cast p2 v)) = x
  obtain rfl : p3 = TypeVec.uLift_append1_ULift_uLift := rfl
  clear *-
  dsimp at x
  cases x using cases
  case hCont x =>
    right
    simp only [dest_cont, Sum.elim_inr, id_eq]
    refine ⟨_, rfl, ?_⟩
    simp only [map_cont, flatten_cont, downMap_transliterateMap_downMap, ← map_map, eq_downMap]
    ext
    simp only [HpLuM.mk_dest]
    rw [downMap_map, TypeVec.appendFun_id_id]
    rfl
  · left
    simp only [dest_recall, Sum.elim_inl]
    rw [map_recall, flatten_recall]
    rfl

@[simp]
theorem futu_flatten
    (f : β → P.uLift (α.uLift ::: Free P α β))
    (seed : β)
    : (futu f seed).dest = downMap (flatten ∘ map (futu f)) (f seed) := by
  rw [futu_flatten_mk, HpLuM.mk_dest]

theorem futu'_flatten_mk
    (f : β → P (α ::: Free P α β))
    (seed : β)
    : futu' f seed = .mk ((TypeVec.id ::: flatten ∘ map (futu' f)) <$$> (f seed)) := by
  dsimp [futu']
  apply HpLuM.bisim_map (fun a b =>
    a = b
    ∨ ∃ x, a = HpLuM.corec' (MvFunctor.map (TypeVec.id ::: Sum.elim f id ∘ dest')) x ∧
           b = HpLuM.mk ((TypeVec.id ::: flatten ∘ map (futu'.{u} f)) <$$> x)
    ) <| .inr ⟨_, rfl, rfl⟩
  rintro _ _ (rfl|⟨x,rfl,rfl⟩)
  · simp
  simp only [map_fst, HpLuM.dest_corec', map_map, TypeVec.appendFun_comp', TypeVec.comp_id,
    Function.const_comp, HpLuM.mk_dest, exists_true_left]
  intro v
  rw! (castMode := .all) [HpLuM.dest_corec', HpLuM.mk_dest]
  simp only [eqRec_eq_cast, map_fst, map_snd, TypeVec.comp.get, TypeVec.append1_get_fz,
    TypeVec.appendFun.get_fz, Function.comp_apply, cast_eq]
  generalize_proofs p
  generalize (x.snd Fin2.fz (cast p v)) = x
  clear *-
  dsimp at x
  cases x using cases'
  · right
    simp only [dest'_cont', Sum.elim_inr, id_eq, map_cont', flatten_cont', map_map,
      TypeVec.appendFun_comp', TypeVec.comp_id]
    refine ⟨_, rfl, rfl⟩
  · left
    simp
    rfl

end Free

end Sme


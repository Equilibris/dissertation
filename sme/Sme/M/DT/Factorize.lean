import Mathlib.Data.PFunctor.Multivariate.W
import Sme.M.DT.Defs

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {α β : Type u} {n : Nat} {P : MvPFunctor (n + 1)} {α : TypeVec n}

namespace DeepThunk

def ofBounded : W P α → HpLuM P α :=
  HpLuM.corec' (wDest' _)

abbrev Finitizable : HpLuM P α → Prop := (∃ bnd, ofBounded bnd = ·)

@[elab_as_elim]
def wp_ind {α : TypeVec n} {C : ∀ x : P.last.W, P.WPath x ⟹ α → Sort _}
    (ih : ∀ (a : P.A) (f : P.last.B a → P.last.W) (f' : P.WPath ⟨a, f⟩ ⟹ α),
        (∀ i : P.last.B a, C (f i) (P.wPathDestRight f' i)) → C ⟨a, f⟩ f') :
    ∀ (x : P.last.W) (f' : P.WPath x ⟹ α), C x f'
  | ⟨a, f⟩, f' => ih a f f' fun _i => wp_ind ih _ _

@[elab_as_elim]
def w_ind' {α : TypeVec n} {C : P.W α → Sort _}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α),
        (∀ i, C (f i)) → C (P.wMk a f' f)) :
    ∀ x, C x := fun x => by
  refine wp_ind (C := (C ⟨·, ·⟩)) (fun a f f' ih' => ?_) x.fst x.snd
  dsimp [wMk] at ih
  have ih'' := ih a (P.wPathDestLeft f') fun i => ⟨f i, P.wPathDestRight f' i⟩
  dsimp at ih''
  have := (cast (by rw [wPathCasesOn_eta]) ih'')
  refine this ih'

theorem dest_Finitizable
    (x : HpLuM P α)
    : Finitizable x ↔ ∀ v, Finitizable <| x.dest.snd .fz v where
  mp := by
    rintro ⟨x, rfl⟩ h
    induction x using w_ind'
    case ih a f' f ih =>
    clear ih
    simp only [Finitizable, ofBounded]
    rw! (castMode := .all) [HpLuM.dest_corec']
    simp
  mpr h := by
    use wMk P x.dest.1 (x.dest.2 ·.fs) (Classical.choose <| h ·)
    apply HpLuM.ext_dest
    simp only [ofBounded, HpLuM.dest_corec']
    refine Sigma.ext rfl <| heq_of_eq <| funext fun | .fz | .fs s => ?_
    <;> dsimp
    <;> rw! (castMode := .all) [P.wDest'_wMk]
    <;> simp only [TypeVec.splitFun.get_fz, TypeVec.splitFun.get_fs]
    ext v
    rw! [←Classical.choose_spec <| h v]
    simp [ofBounded]

variable {α : TypeVec (n + 1)}

def nFinDT (x : DeepThunk P α)
    (h : ¬Finitizable x)
    (f : α .fz → α .fz)
    : TypeVec.splitFun TypeVec.id f <$$> x = x := by
  apply HpLuM.bisim_map fun a b =>
    ∃ x, b = x
    ∧ a = TypeVec.splitFun TypeVec.id f <$$> x
    ∧ ¬Finitizable x
  · exact ⟨_, rfl, rfl, h⟩
  rintro _ x ⟨_, rfl, rfl, h⟩
  rw [HpLuM.dest_map]
  rw! (castMode := .all) [MvFunctor.map_map]
  rw! (castMode := .all) [TypeVec.appendFun_comp']
  dsimp
  /- simp only [comp.B_eq, ↓existsAndEq, map_fst, not_exists, true_and, HpLuM.dest_map] -/
  sorry

end DeepThunk

end Sme


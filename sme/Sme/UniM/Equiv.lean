import Sme.UniM.SM

open PFunctor

namespace Sme.SM

universe u v w

variable {n} {P : PFunctor.{u, v}}

@[elab_as_elim]
def mk_cases
    {motive : P.M → Sort _}
    (h : ∀ x, motive (M.mk x))
    x : motive x :=
  cast (by simp only [M.mk_dest]) <| h x.dest

def bisim_map
    (R : P.M → P.M → Prop)
    {a b}
    (hRel : R a b)
    (h : ∀ s t, R s t →
          ∃ h : (Function.const _ PUnit.unit) <$> s.dest
              = (Function.const _ PUnit.unit) <$> t.dest,
          ∀ v, R (s.dest.snd v) (t.dest.snd (cast (by
            rw [show s.dest.fst = t.dest.fst from (Sigma.ext_iff.mp h).1]) v)))
    : a = b := by
  apply M.bisim R
  case a => exact hRel
  clear *-h
  intro x y r
  cases x using mk_cases; next x =>
  cases y using mk_cases; next y =>
  rcases x with ⟨xf, xs⟩
  rcases y with ⟨yf, ys⟩
  simp only [M.dest_mk]
  have ⟨hfst, hrest⟩ := h _ _ r
  dsimp at hfst hrest
  obtain rfl : xf = yf := (Sigma.ext_iff.mp hfst).1
  refine ⟨xf, xs, ys, rfl, rfl, fun i => hrest i⟩

def equivP : SM.{u, v, max u v w} P ≃ M.{u, v} P where
  toFun  := M.corec SM.dest
  invFun x := SM.uLift.{u, v, _, _} <| SM.corec (P := P) M.dest x

  left_inv  x := by
    refine bisim ⟨fun a b => a = (corec M.dest (M.corec dest b)).uLift, ?_, rfl⟩
    rintro s t rfl
    refine ⟨rfl, fun v => rfl⟩
  right_inv x := by
    apply bisim_map (fun a b => a = M.corec dest (corec M.dest b).uLift) rfl
    rintro x y rfl
    simp only [cast_eq, M.dest_corec, map_eq_map, PFunctor.map_map, Function.const_comp,
      exists_prop]
    use rfl
    intro v
    rw! (castMode := .all) [M.dest_corec, dest_uList, dest_corec, PFunctor.map_map]
    rfl


import Sme.M.HpLuM
import Sme.EquivP
import Mathlib.Control.Functor.Multivariate

open scoped MvFunctor

namespace Sme

universe u v w x y z

variable
    {n : Nat}
    {F : TypeVec.{u} (n + 1) → Type v}
    {α : TypeVec.{u} n}
    {P : MvPFunctor (n + 1)}
    [EquivP F P]

def HpLuME {P} (F : TypeVec.{u} (n + 1) → Type v) (α : TypeVec.{u} n) [EquivP F P] : Type u :=
  HpLuM P α

namespace HpLuME

def dest : HpLuME F α → F (α ::: HpLuME F α) :=
  EquivP.equiv ∘ HpLuM.dest

def corec
    {β : Type u}
    (gen : β → F (α ::: β))
    : β → HpLuME F α :=
  HpLuM.corec' (EquivP.equiv.symm ∘ gen)

@[simp]
theorem dest_corec
    {β : Type u}
    (gen : β → F (α ::: β))
    (g : β)
    : dest (corec gen g) = (TypeVec.id ::: corec gen) <$$> gen g := by
  dsimp [dest, corec]
  rw [HpLuM.dest_corec']
  rfl

def mk : F (α ::: HpLuME F α) → HpLuME F α := 
  HpLuM.mk ∘ EquivP.equiv.symm

@[simp]
theorem dest_mk
    {v : HpLuME F α}
    : mk (dest v) = v := by
  dsimp [dest, mk]
  rw [Equiv.symm_apply_apply, HpLuM.dest_mk]

@[simp]
theorem mk_dest
    {v : F (α ::: HpLuME F α)}
    : dest (mk v) = v := by
  dsimp [dest, mk]
  rw [HpLuM.mk_dest, Equiv.apply_symm_apply]

end Sme.HpLuME


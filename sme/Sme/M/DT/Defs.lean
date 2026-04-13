import Sme.PFunctor.EquivP
import Sme.PFunctor.Prj
import Sme.M.HpLuM
import Sme.M.DT.DTSum
import Sme.Vec
import Sme.HEq

namespace Sme

open MvPFunctor
open scoped MvFunctor

universe u v w

variable {α β : Type u} {n : Nat}

namespace DeepThunk
abbrev innerMapper {n} : Vec (MvPFunctor n.succ) n
  | .fz => .comp DTSum !![.prj <| .fs .fz, .prj .fz]
  | .fs n => .prj (n.add 2)

@[simp]
theorem innerMapper_fz
    : innerMapper (n := n.succ) Fin2.fz
    = .comp DTSum !![.prj <| .fs .fz, .prj .fz] := rfl

@[simp]
theorem innerMapper_fs {i : Fin2 n}
    : innerMapper (.fs i)
    = .prj (i.add 2) := rfl

abbrev innerMapperC {n} : Vec (CurriedTypeFun n.succ) n
  | .fz => .comp (show CurriedTypeFun 2 from Sum) !![.prj <| .fs .fz, .prj .fz]
  | .fs n => .prj (n.add 2)

instance {n} : {i : Fin2 n} → EquivP _ (innerMapperC i) (innerMapper i)
  | .fz => by
    apply EquivP.comp' inferInstance
    rintro (_|_|_|_)
    <;> dsimp
    <;> infer_instance
  | .fs _ => by dsimp [innerMapperC, innerMapper]; infer_instance

-- Takes a functor P α β γ ⋯, and maps it to P (ξ ⊕ α) β γ ⋯
abbrev NatTrans {n} (P : MvPFunctor n) : MvPFunctor (n + 1) := .comp P innerMapper
end DeepThunk

def DeepThunk {n} (P : MvPFunctor n) := HpLuM (DeepThunk.NatTrans P)

instance {n} {P : MvPFunctor n} : MvFunctor <| DeepThunk P := HpLuM.instMvFunctor
instance {n} {P : MvPFunctor n} : LawfulMvFunctor <| DeepThunk P := HpLuM.instLawfulMvFunctor

namespace DeepThunk

-- TODO: Change this to use ⊕ instead of DTSum
def DTComp (F : CurriedTypeFun.{u, v} n) : CurriedTypeFun.{u, v} n.succ :=
  .comp F innerMapperC

instance (priority := 100) {n} {F : CurriedTypeFun.{u, v} n} {P} [efp : EquivP _ F P]
    : EquivP _ (DTComp F) (NatTrans P) := by
  dsimp [DTComp]
  infer_instance

end Sme.DeepThunk


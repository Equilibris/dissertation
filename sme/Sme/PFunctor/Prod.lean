import Sme.ForMathlib.Data.PFunctor.Multivariate.Basic
import Sme.ForMathlib.Data.TypeVec
import Mathlib.Tactic.DepRewrite
import Mathlib.Order.Extension.Linear
import Sme.PFunctor.NatTrans

namespace MvPFunctor

open scoped MvFunctor

universe u

variable {n : Nat}

def prod (P Q : MvPFunctor.{u} n) : MvPFunctor n where
  A := P.1 × Q.1
  B p i := P.2 p.1 i ⊕ Q.2 p.2 i

namespace prod

variable {P Q : MvPFunctor n}

def fst : NatTrans (prod P Q) P where
  hd := Prod.fst
  child _ _ := Sum.inl

def snd : NatTrans (prod P Q) Q where
  hd := Prod.snd
  child _ _ := Sum.inr

def mk {R} (f : NatTrans R P) (g : NatTrans R Q) : NatTrans R (prod P Q) where
  hd h := ⟨f.1 h, g.1 h⟩
  child _ i := Sum.elim (f.child _ i) (g.child _ i)

theorem fst_mk {R} {f : NatTrans R P} {g : NatTrans R Q}
    : ((mk f g).comp fst) = f := rfl
theorem snd_mk {R} {f : NatTrans R P} {g : NatTrans R Q}
    : ((mk f g).comp snd) = g := rfl

def map {P' Q'} (f : NatTrans P' P) (g : NatTrans Q' Q) : NatTrans (prod P' Q') (prod P Q) where
  hd := Prod.map f.1 g.1
  child _ i := Sum.map (f.2 _ i) (g.2 _ i)

theorem fst_map {P' Q'} {f : NatTrans P' P} {g : NatTrans Q' Q}
    : ((map f g).comp fst) = fst.comp f := rfl
theorem snd_map {P' Q'} {f : NatTrans P' P} {g : NatTrans Q' Q}
    : ((map f g).comp snd) = snd.comp g := rfl

end prod


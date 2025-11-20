import Sme.M.SDefs

inductive IsEven : Nat → Type
  | zEven : IsEven 0
  | ssEven {n} : IsEven n → IsEven (n.succ.succ)

example : Sigma IsEven := sorry


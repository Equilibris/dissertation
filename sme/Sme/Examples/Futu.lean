import Sme.M.Futu
import Sme.Examples.Stream

open Sme Free

open scoped MvFunctor

variable {α}

def nats : Nat → SS Nat := .corec' (fun n => SS.mk n n.succ)

/-- info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] -/
#guard_msgs in
#eval (nats 0).take 20

def interlace_const (o : α) (v : SS α)
    : SS α := .corec' body ⟨v, .true⟩
where body : SS α × Bool → _
  | ⟨v, .true⟩ =>
    have ⟨hd, tl⟩ := v.dest
    SS.mk hd ⟨tl, .false⟩
  | ⟨v, .false⟩ => SS.mk o ⟨v, .true⟩

/-- info: [1, 0, 2, 0, 3, 0, 4, 0, 5, 0] -/
#guard_msgs in
#eval! (interlace_const 0 (nats 1)).take 10

def interlace_const' (o : α)
    : SS α → SS α := futu' body
where body s :=
  have ⟨hd, tl⟩ := s.dest
  SS.mk hd <| cont' <| SS.mk o <| recall tl

/-- info: [1, 0, 2, 0, 3, 0, 4, 0, 5, 0] -/
#guard_msgs in
#eval! (interlace_const' 0 (nats 1)).take 10

def stutter (v : SS α)
    : SS α := .corec' body ⟨v, .true⟩
where body : SS α × Bool → _
  | ⟨v, .true⟩ =>
    have ⟨hd, _⟩ := v.dest
    SS.mk hd ⟨v, .false⟩
  | ⟨v, .false⟩ =>
    have ⟨hd, tl⟩ := v.dest
    SS.mk hd ⟨tl, .true⟩

/-- info: [0, 0, 1, 1, 2, 2, 3, 3, 4, 4] -/
#guard_msgs in
#eval! (stutter (nats 0)).take 10

def stutter'
    : SS α → SS α := futu' body
where body s :=
  have ⟨hd, tl⟩ := s.dest
  SS.mk hd <| cont' <| SS.mk hd <| recall tl

/-- info: [0, 0, 1, 1, 2, 2, 3, 3, 4, 4] -/
#guard_msgs in
#eval! (stutter' (nats 0)).take 10

def RLE_decode
    (s : SS (α × Nat))
    : SS α := .corec' f s.dest where
  f
  | ⟨⟨v, 0  ⟩, r⟩ => SS.mk v r.dest
  | ⟨⟨v, n+1⟩, r⟩ => SS.mk v ⟨⟨v, n⟩, r⟩

/-- info: [0, 1, 1, 2, 2, 2, 3, 3, 3, 3] -/
#guard_msgs in
#eval! (RLE_decode ((fun | .fz, a => Prod.mk a a)
  <$$> nats 0)).take 10

def RLE_decode'
    : SS (α × Nat) → SS α := Free.futu' f where
  f x :=
    have ⟨⟨v, n⟩, r⟩ := x.dest
    iter v r n
  iter v r
    | 0   => SS.mk v <| .recall r
    | n+1 => SS.mk v <| .cont' <| iter v r n

/-- info: [0, 1, 1, 2, 2, 2, 3, 3, 3, 3] -/
#guard_msgs in
#eval! (RLE_decode' ((fun | .fz, a => Prod.mk a a)
  <$$> nats 0)).take 10


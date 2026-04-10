type ('a, 'b) listF = Nil | Cons of 'a * 'b
type 'a ilist = Mk of (('a, 'a ilist) listF)

let mk x = Mk (x)
let dest = function | Mk v -> v
let rec fold bh ih = function
    | Mk(Nil) -> bh | Mk(Cons(h, t)) -> ih h (fold bh ih t)

type 'a icolist = CMk of (unit -> ('a, 'a icolist) listF)

let mk x = CMk (fun _ -> x)
let dest = function | CMk v -> v ()
let rec unfold gen v = CMk (fun _ ->
    match gen v  with
    | Nil -> Nil
    | Cons(h, t) -> Cons(h, unfold gen t))

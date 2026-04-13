#let Type = $bold("Type")$
#let takeL(f, s, e) = f.split("\n").slice(s,e).join("\n")
#let partL(f, ..args) = {
  let args = (0,) + args.pos() + (none,)
  let f = f.split("\n")

  args.zip(args.slice(1)).map(((a,b)) => f.slice(a,b).join("\n"))
}


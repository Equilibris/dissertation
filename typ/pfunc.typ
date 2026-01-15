#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

/*
*
* I want to be able to declare polynomials in a format like this
*
*
*/

#let sum = (
  legend : (($alpha$, $beta$),),
  ctors : (
    inl : ( body : (($0$, $1$), ), ),
    inr : ( body : (($1$, $0$), ), ),
  )
)

#let prj = (
  legend : (($alpha_0$,), ($alpha_n$,), ($alpha_i$, )),
  ctors : (
    mk : (body : (($0$, ), ($1$, ), ($0$, )),),
  )
)

#let list = (
  legend : (($alpha$,), ),
  ctors : (
    mk : (
      body : (($"Fin" n$, ), ),
      param : $(n : NN)$
    ),
  )
)

#let const(T) = (
  legend : (($alpha_0$,), ($alpha_i$,)),
  ctors : (
    "mk" : (
      body : (($0$,), ($0$,)),
      param : $(v : #T)$,
    ),
  )
)

#let genp = (
  legend : (($alpha_0$,), ($alpha_i$,)),
  ctors : (
    "h0" : (
      body : (($c_(0,v)$,), ($c_(i,v)$,)),
      param : $(v : h_0)$,
      lab : $k_0$
    ),
    "cont" : (
      body : (($dots$,), ($dots$,)),
      lab : $dots$,
      dots : $dots.up$,
    ),
    "hj" : (
      body : (($c_(0,v)$,), ($c_(i,v)$,)),
      param : $(v : h_j)$,
      lab : $k_j$
    ),
  )
)

#let scan(arr, init, f) = arr.fold((init, ), (acc, x) => {
  acc.push(f(acc.last(), x))

  acc
})

#let show_ctors(nm, (x, y), decl) = {
  let labs = ()
  edge((x + - .5, y - .5), (x + (decl.len() - .5), y - .5), "..")

  for (i, (k, v)) in decl.pairs().enumerate() {
    let x_sh = i
    let body = v.body

    let lnm = label(nm + "-" + k)
    labs.push(lnm)

    node((x + x_sh, y), [ #v.at("lab", default : k) #v.at("param", default: none) ], name : lnm)

    for (i, (ib, skip)) in body.zip(scan(body, 0, (acc, v) => acc + v.len())).enumerate() {
      for (j, n) in ib.enumerate() {
        let j = j + skip
        let arg = label(nm + "-" + k + "-" + "c" + str(j))

        labs.push(arg)

        node((x + x_sh, y - j - 1), n, name : arg)
      }

      if i != 0 {
        node((x + x_sh, -skip + -.5), v.at("dots", default : $dots.v$))
      }
    }

    if i < decl.len() - 1 {
      edge((x + i + 0.5, y + .5), (x + i + 0.5, y - body.map(v => v.len()).sum() - 0.5), "-")
    }
    if i == 0 {
      edge((x - 0.5, y + .5), (x - 0.5, y - body.map(v => v.len()).sum() - 0.5), "..")
    }
    if i == decl.len() - 1 {
      edge((x + i + 0.5, y + .5), (x + i + 0.5, y - body.map(v => v.len()).sum() - 0.5), "..")
    }
  }

  // node((0,0), enclose: labs, fill: luma(95%))
}

#let show_decl(nm, (x, y), decl) = {
  let labs = ()

  for (i, (ib, skip)) in decl.legend
      .zip(scan(decl.legend, 0, (acc, v) => acc + v.len()))
      .enumerate() {
    for (j, n) in ib.enumerate() {
      let j = j + skip
      let arg = label(nm + "-c" + str(j))
      labs.push(arg)
      node((x, y - j - 1), n, name : arg)
    }

    if i != 0 {
      node((x, -skip + -.5), $dots.v$)
    }
  }

  show_ctors(nm, (x + 1, y), decl.ctors)
}

#let show_obj(
    nm, (x, y),
    decl, ctor, funs,
    params : none,
    gap : 1,
    term : none,
    releg : none
  ) = {
  let cnm = label(nm + "-nm")

  let labs = (cnm,)
  let selectedCtor = decl.ctors.at(ctor)

  edge((x + - .5, y - .5), (x + .5 + gap, y - .5), "..")
  node((x + gap / 2, y), [#selectedCtor.at("lab", default : ctor) #params], name : cnm)

  if term != none {
    edge((x + - .5, y + .5), (x + .5 + gap, y + .5), "..")
    node((x + gap / 2, y + 1), term)
  }

  let leg = if releg != none { releg } else { decl.legend }

  for (i, (ib, skip)) in leg
      .zip(scan(leg, 0, (acc, v) => acc + v.len()))
      .enumerate() {
    for (j, n) in ib.enumerate() {
      let jv = j + skip

      let argl = label(nm + "-c" + str(jv) + "-l")
      let argr = label(nm + "-c" + str(jv) + "-r")

      labs.push(argl)
      labs.push(argr)

      let rhs = selectedCtor.body.at(i).at(j)

      node((x, y - jv - 1), n, name : argl)
      node((x + gap, y - jv - 1), rhs, name : argr)
      // node((x, y - jv - 1), n, name : argl)
      // node((x + gap, y - jv - 1), rhs, name : argr)
      edge(argr, argl, funs.at(i).at(j), "->")
    }

    if i != 0 {
      node((x, -skip + -.5), $dots.v$)
      node((x + gap, -skip + -.5), $dots.v$)
    }
  }

  // node(enclose : labs, fill: rgb(0, 0, 0, 10%), inset : 6mm, layer : -1)
}

#let show_map(nm, (x, y), lhs, rhs, funs, gap : 1) = {
  let labs = ()
  let cnm = label(nm + "-nm")

  edge((x + - .5, y - .5), (x + .5 + gap, y - .5), "..")
  node((x + gap / 2, y), [`<$>`], name : cnm)

  for (i, (ib, skip)) in lhs
      .zip(scan(lhs, 0, (acc, v) => acc + v.len()))
      .enumerate() {
    for (j, n) in ib.enumerate() {
      let jv = j + skip

      let argl = label(nm + "-c" + str(jv) + "-l")
      let argr = label(nm + "-c" + str(jv) + "-r")

      labs.push(argl)
      labs.push(argr)

      let rhs = rhs.at(i).at(j)

      node((x, y - jv - 1), n, name : argl)
      node((x + gap, y - jv - 1), rhs, name : argr)
      // node((x, y - jv - 1), n, name : argl)
      // node((x + gap, y - jv - 1), rhs, name : argr)
      edge(argr, argl, funs.at(i).at(j), "->")
    }

    if i != 0 {
      node((x, -skip -.5), $dots.v$)
      node((x + 1, -skip -.5), $dots.v$)
    }
  }
}


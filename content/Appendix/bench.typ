#import "../utils.typ": *

== Benchmarking code

#let f = read("../../sme/Sme/Bench.lean")

#raw(f, block:true, lang:"lean")

#let f = read("../../ista-plv-coinductive/Bench.lean")

#raw(f, block:true, lang:"lean")

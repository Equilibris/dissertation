import Lake
open Lake DSL

package "sme" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
  ]

/- require "leanprover-community" / "mathlib" -/
require mathlib from git "https://github.com/Equilibris/mathlib4" @ "d6b32558033a0b7f9a32a64906a9095aaf46023f"
require CoinductivePredicates from git "https://github.com/Equilibris/CoinductivePredicates" @ "main"

@[default_target]
lean_lib Sme where
  -- add any library configuration options here

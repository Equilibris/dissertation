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
require mathlib from git "https://github.com/Equilibris/mathlib4" @ "289a8933c6c4ec9da33768253521116ed7527e48"
require CoinductivePredicates from git "https://github.com/Equilibris/CoinductivePredicates" @ "main"

@[default_target]
lean_lib «Sme» where
  -- add any library configuration options here

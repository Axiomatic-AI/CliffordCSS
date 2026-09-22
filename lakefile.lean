import Lake

open Lake DSL

package cliffordCSS where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

/-- Mathlib, pinned to the exact commit this development was checked against. -/
require "leanprover-community" / "mathlib" @ git "e560e3ad639d2d8c4c0662784bd40c8b07797781"

@[default_target]
lean_lib CliffordCSS where

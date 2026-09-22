import Mathlib.Data.ZMod.Basic

/-!
# The two-element case split for `𝔽₂ = ZMod 2`

Pure mathematics : the single canonical copy of the trivial fact that
every element of `ZMod 2` is `0` or `1`. It is hoisted into this minimal, dependency-free home so
the several this library developments that need the `𝔽₂` dichotomy (e.g.
`PauliStringEncodingStandardForm`, `CliffordSymplecticLevi`) share one copy rather than each
re-declaring it.

The statement names only `ZMod 2` — no matrix carrier.
-/

namespace CliffordCSS

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

end CliffordCSS

import CliffordCSS.Gates.Pauli
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import CliffordCSS.ToMathlib.Analysis.Normed.Algebra.ExponentialInvolution
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The exponential of `i θ (n · σ)` (Nielsen & Chuang, Exercise 2.35)

For a real *unit* three-vector `n` and a real angle `θ`, the exponential of `i θ (n · σ)` has the
closed form

`exp (i θ (n · σ)) = cos θ • I + i sin θ • (n · σ)`.

This is pure `2 × 2` complex-matrix mathematics : the matrix exponential is Mathlib's
`NormedSpace.exp`, and the statement names only the concrete combination `pauliDot n = n · σ`,
raw matrices, and the real trigonometric functions.

## Proof

The whole content is the involution `(n · σ)² = I` for a unit vector
(`pauliDot_mul_self_of_unit`): writing the exponent as `z • (n · σ)` with `z = θ * i`, the general
`NormedSpace.exp_smul_of_mul_self_eq_one` gives `cosh z • I + sinh z • (n · σ)`, and
`Complex.cosh_mul_I` / `Complex.sinh_mul_I` turn `cosh (θ i) = cos θ` and `sinh (θ i) = (sin θ) i`
into the trigonometric form. The matrix exponential needs a norm to name its series; we supply the
`ℓ^∞`-operator norm locally via `open scoped Matrix.Norms.Operator`, exactly as Mathlib's own
`Matrix.exp_*` lemmas do (the norm choice does not affect the value of `exp`).

## Main results

* `pauliDot_exp_of_unit`: `exp (i θ (n · σ)) = cos θ • I + i sin θ • (n · σ)` for a unit vector `n`.
-/

namespace CliffordCSS

open NormedSpace

/-- **Nielsen & Chuang, Exercise 2.35** (exponential of the Pauli matrices). For a real unit vector
`n` (`n₀² + n₁² + n₂² = 1`) and a real angle `θ`,
`exp (i θ (n · σ)) = cos θ • I + i sin θ • (n · σ)`,
where `n · σ = pauliDot n`.

The exponent `i θ (n · σ)` is written as `(θ * i) • pauliDot n`. Since `(n · σ)² = I` for a unit
vector (`pauliDot_mul_self_of_unit`), this is the case `a = pauliDot n`, `x = θ` of the general
Euler formula for an involution `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one`. -/
theorem pauliDot_exp_of_unit {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) :
    exp (((θ : ℂ) * Complex.I) • pauliDot n)
      = (Real.cos θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + ((Real.sin θ : ℂ) * Complex.I) • pauliDot n := by
  open scoped Matrix.Norms.Operator in
  exact exp_smul_mul_I_of_mul_self_eq_one (pauliDot_mul_self_of_unit hn) θ

end CliffordCSS

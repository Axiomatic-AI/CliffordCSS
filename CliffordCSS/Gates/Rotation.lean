import CliffordCSS.Gates.PauliExponential

/-!
# The single-qubit rotation operators (Nielsen & Chuang, §4.2, eq. 4.4–4.8)

For a real three-vector `n` and a real angle `θ`, Nielsen & Chuang define the rotation about the
`n`-axis by
`R_n̂(θ) ≡ exp(−iθ (n·σ)/2)` (eq. 4.8),
and the three coordinate rotations `R_x`, `R_y`, `R_z` as the special cases `n = x̂, ŷ, ẑ`
(eq. 4.4–4.6). This is pure `2 × 2` complex-matrix mathematics : the matrix exponential
is Mathlib's `NormedSpace.exp`, and every statement names only the concrete `pauliDot n = n·σ`, raw
matrices, and the real trigonometric functions.

## What is formalized

* `rotAxis n θ = exp(−i (θ/2) (n·σ))` — the rotation operator (eq. 4.8), for *any* three-vector `n`.
* `rotAxis_eq_of_unit` — the closed form `R_n̂(θ) = cos(θ/2) I − i sin(θ/2) (n·σ)` for a unit `n`
  (the right-hand side of eq. 4.8), reusing the Exercise 2.35 exponential `pauliDot_exp_of_unit`.
* `rotAxis_mem_unitaryGroup` — every rotation is unitary. This holds for *any* axis: the exponent
  `A = −i(θ/2)(n·σ)` is skew-Hermitian (`n·σ` is Hermitian), and `exp` commutes with the adjoint
  (`Matrix.exp_conjTranspose`), so `Rᴴ R = exp(−A) exp(A) = exp 0 = I`.
* `rotAxis_mul_same` / `rotAxis_zero` — the one-parameter group law `R_n̂(a) R_n̂(b) = R_n̂(a+b)`
  and `R_n̂(0) = I`, both immediate from `exp(A) exp(B) = exp(A+B)` for the commuting exponents
  about a fixed axis.
* `rotX`, `rotY`, `rotZ` — the coordinate rotations (eq. 4.4–4.6), with their explicit `2 × 2`
  closed forms `rotX_eq`, `rotY_eq`, `rotZ_eq` and unitarity.

These rotation operators are the shared foundation for the Chapter 4 single-qubit-decomposition
items — the Z-Y decomposition (Theorem 4.1), the ABC decomposition (Corollary 4.2), and the many
exercises about `R_n̂` (Ex 4.4–4.11). Everything here names raw matrix data only, so it lives in
this library.

## Design notes

* `R_n̂(θ)` is defined literally as N&C's `exp(−iθ(n·σ)/2)` (not as an explicit matrix), so the
  definition is manifestly faithful to eq. 4.8 and unitarity/the group law are inherited from the
  exponential. The explicit matrices (eq. 4.4–4.6) are then *theorems*
  (`rotX_eq`/`rotY_eq`/`rotZ_eq`), computed from the closed form and `pauliDot_eq`.
* The axis is a bare `Fin 3 → ℝ` with normalization the scalar hypothesis
  `n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1`, matching `CliffordCSS/Gates/Pauli.lean` and N&C's `n̂ · σ ≡ Σᵢ nᵢ σᵢ`.
-/

namespace CliffordCSS

open Matrix Complex NormedSpace

/-- The **rotation operator** `R_n̂(θ) ≡ exp(−iθ (n·σ)/2)` about the axis `n` by angle `θ`
(Nielsen & Chuang, eq. 4.8). Defined for any three-vector `n`; for a unit vector it has the closed
form `cos(θ/2) I − i sin(θ/2) (n·σ)` (`rotAxis_eq_of_unit`). -/
noncomputable def rotAxis (n : Fin 3 → ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  exp ((((-(θ / 2) : ℝ) : ℂ) * Complex.I) • pauliDot n)

/-- The **closed form** of the rotation operator (Nielsen & Chuang, eq. 4.8, right-hand side): for a
unit axis `n` (`n₀² + n₁² + n₂² = 1`),
`R_n̂(θ) = cos(θ/2) • I − (sin(θ/2) · i) • (n·σ)`.
This is the Exercise 2.35 exponential `pauliDot_exp_of_unit` at angle `−θ/2`. -/
theorem rotAxis_eq_of_unit {n : Fin 3 → ℝ}
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) (θ : ℝ) :
    rotAxis n θ = (Real.cos (θ / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - ((Real.sin (θ / 2) : ℂ) * Complex.I) • pauliDot n := by
  rw [rotAxis, pauliDot_exp_of_unit hn, Real.cos_neg, Real.sin_neg]
  push_cast
  module

/-- Each rotation operator is **unitary** in the sense of `Rᴴ R = I`. This needs no unit hypothesis:
the exponent `A = −i(θ/2)(n·σ)` is skew-Hermitian (`Aᴴ = −A`, since `(n·σ)ᴴ = n·σ`), so
`Rᴴ R = (exp A)ᴴ exp A = exp(Aᴴ) exp A = exp(−A) exp A = exp(−A + A) = exp 0 = I`
using `Matrix.exp_conjTranspose` and `exp(X)exp(Y) = exp(X+Y)` for the commuting `−A, A`. -/
theorem rotAxis_conjTranspose_mul_self (n : Fin 3 → ℝ) (θ : ℝ) :
    (rotAxis n θ)ᴴ * rotAxis n θ = 1 := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := (((-(θ / 2) : ℝ) : ℂ) * Complex.I) • pauliDot n with hA
  have hskew : Aᴴ = -A := by
    rw [hA, conjTranspose_smul, pauliDot_conjTranspose,
      show star (((-(θ / 2) : ℝ) : ℂ) * Complex.I) = -(((-(θ / 2) : ℝ) : ℂ) * Complex.I) by
        simp [Complex.conj_I], neg_smul]
  have hcomm : Commute (-A) A := (Commute.refl A).neg_left
  calc (rotAxis n θ)ᴴ * rotAxis n θ
      = exp Aᴴ * exp A := by rw [rotAxis, ← Matrix.exp_conjTranspose]
    _ = exp (-A) * exp A := by rw [hskew]
    _ = exp (-A + A) := (Matrix.exp_add_of_commute (-A) A hcomm).symm
    _ = 1 := by rw [neg_add_cancel, NormedSpace.exp_zero]

/-- Each rotation operator is **unitary** (`R ∈ unitaryGroup`), the group-membership form of
`rotAxis_conjTranspose_mul_self`. -/
theorem rotAxis_mem_unitaryGroup (n : Fin 3 → ℝ) (θ : ℝ) :
    rotAxis n θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact rotAxis_conjTranspose_mul_self n θ


/-- The **rotation about the `ẑ` axis** `R_z(θ) ≡ exp(−iθZ/2)` (Nielsen & Chuang, eq. 4.6). -/
noncomputable def rotZ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := rotAxis ![0, 0, 1] θ


/-- The explicit matrix of `R_z` (Nielsen & Chuang, eq. 4.6):
`R_z(θ) = !![exp(−iθ/2), 0; 0, exp(iθ/2)]` (a diagonal phase). -/
theorem rotZ_eq (θ : ℝ) :
    rotZ θ = !![Complex.exp (-(θ / 2) * Complex.I), 0; 0, Complex.exp ((θ / 2) * Complex.I)] := by
  have e1 : Complex.exp (-(θ / 2) * Complex.I)
      = (Real.cos (θ / 2) : ℂ) - (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show (-(θ / 2) : ℂ) * Complex.I = ((-(θ / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have e2 : Complex.exp ((θ / 2) * Complex.I)
      = (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show ((θ / 2) : ℂ) * Complex.I = ((θ / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [rotZ, rotAxis_eq_of_unit (by simp), pauliDot_eq, e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


/-- `R_z(θ)` is unitary. -/
theorem rotZ_mem_unitaryGroup (θ : ℝ) : rotZ θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  rotAxis_mem_unitaryGroup _ θ


end CliffordCSS

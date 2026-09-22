import CliffordCSS.Gates.Hadamard
import CliffordCSS.Gates.Pauli

/-!
# Conjugating the Pauli matrices by the Hadamard gate (Nielsen & Chuang, Exercise 4.13)

Nielsen & Chuang, Exercise 4.13 (*Circuit identities*, p. 177) asks to prove the three
Hadamard-conjugation identities (eq. 4.18)

`H X H = Z`, `H Y H = -Y`, `H Z H = X`.

Each is a pure `2 × 2` complex-matrix identity : every statement names only the
concrete Hadamard matrix `hadamardC` (`CliffordCSS/Gates/Hadamard.lean`) and the Pauli matrices
`pauliX`/`pauliY`/`pauliZ` (`CliffordCSS/Gates/Pauli.lean`).

## What is formalised

* `hadamardC_mul_pauliX_mul_hadamardC` — `H X H = Z`.
* `hadamardC_mul_pauliY_mul_hadamardC` — `H Y H = -Y`.
* `hadamardC_mul_pauliZ_mul_hadamardC` — `H Z H = X`.

Geometrically the Hadamard gate is the reflection of the Bloch sphere that exchanges the `x̂` and
`ẑ` axes and flips `ŷ`; the three identities record exactly that action on the Pauli operators.

## Why these live here

These are reusable Chapter-4 infrastructure. The X–Y decomposition (Exercise 4.10) already relies
on Hadamard conjugation exchanging the `x̂`/`ẑ` axes — its `hadamardC_mul_rotZ_mul_hadamardC`
(`H R_z(θ) H = R_x(θ)`) is precisely the rotation-level shadow of `H Z H = X` here. Stating the
three Pauli identities on their own makes that geometric fact citable directly (and matches the
naming convention `hadamardC_mul_<σ>_mul_hadamardC` of the rotation conjugation lemmas).

## Design notes

* **Proof idiom: factor the normalisation, then compute entrywise.** Writing
  `H = (√2)⁻¹ • !![1,1;1,-1]`, the two `H` factors of a conjugation contribute
  `(√2)⁻¹ · (√2)⁻¹ = 2⁻¹` (`inv_sqrt_two_mul_self`), collapsing the Hadamard normalisation to a
  single `2⁻¹ •` in front of `!![1,1;1,-1] * σ * !![1,1;1,-1]`. The remaining `2 × 2` matrix
  equality is checked entry by entry (`fin_cases` on both indices, `Matrix.mul_apply` +
  `Fin.sum_univ_two`, closed by `ring`). This is the same reduce-and-compute idiom as
  `hadamardC_mul_rotZ_mul_hadamardC` / `hadamardC_mul_rotY_mul_hadamardC` in
  this library.
-/

namespace CliffordCSS

open Matrix Complex

/-- **Nielsen & Chuang, Exercise 4.13 (eq. 4.18)**: conjugating `X` by the Hadamard gate gives `Z`,
`H X H = Z`. The Hadamard reflection exchanges the `x̂` and `ẑ` Bloch axes. -/
theorem hadamardC_mul_pauliX_mul_hadamardC : hadamardC * pauliX * hadamardC = pauliZ := by
  rw [hadamardC, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_two_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ] <;> ring

/-- **Nielsen & Chuang, Exercise 4.13 (eq. 4.18)**: conjugating `Y` by the Hadamard gate negates it,
`H Y H = -Y`. The Hadamard reflection flips the `ŷ` Bloch axis. -/
theorem hadamardC_mul_pauliY_mul_hadamardC : hadamardC * pauliY * hadamardC = -pauliY := by
  rw [hadamardC, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_two_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.neg_apply] <;> ring

/-- **Nielsen & Chuang, Exercise 4.13 (eq. 4.18)**: conjugating `Z` by the Hadamard gate gives `X`,
`H Z H = X`. The Hadamard reflection exchanges the `ẑ` and `x̂` Bloch axes; this is the Pauli-level
form of `hadamardC_mul_rotZ_mul_hadamardC` (`H R_z(θ) H = R_x(θ)`). -/
theorem hadamardC_mul_pauliZ_mul_hadamardC : hadamardC * pauliZ * hadamardC = pauliX := by
  rw [hadamardC, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_sqrt_two_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ] <;> ring

end CliffordCSS

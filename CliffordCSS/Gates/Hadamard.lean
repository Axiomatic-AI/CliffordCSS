import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.LinearCombination

/-!
# The Hadamard matrix and its `n`-fold tensor (Kronecker) power

This file is pure mathematics : it defines the single-qubit
Hadamard matrix `H` and its `n`-fold tensor power `H^{⊗n}` over `ℝ`, proves the closed
entry formula of Nielsen & Chuang, Exercise 2.33 (p. 74), and — for the qubit *operator*
work of Chapter 2 — the complex-entried Hadamard `H` together with its Hermiticity,
involution `H² = I`, and unitarity (membership in `Matrix.unitaryGroup`).

## The exercise

N&C write the one-qubit Hadamard operator (eq. 2.54) as
`H = (1/√2) [(|0⟩ + |1⟩)⟨0| + (|0⟩ − |1⟩)⟨1|]`, i.e. the real `2 × 2` matrix
`(1/√2) !![1, 1; 1, -1]`, and ask to show that the Hadamard transform on `n` qubits
`H^{⊗n}` may be written (eq. 2.55) as
`H^{⊗n} = (1/√(2ⁿ)) ∑_{x,y} (-1)^{x·y} |x⟩⟨y|`,
where `x, y` range over `n`-bit strings and `x·y = ∑ᵢ xᵢ yᵢ` is the bitwise dot product.
Finally it asks for an explicit matrix for `H^{⊗2}`.

## What is formalised

* `hadamard` — the `2 × 2` real matrix `(√2)⁻¹ • !![1, 1; 1, -1]` of eq. (2.54), and
  `hadamard_apply` — its entrywise closed form `H a b = (√2)⁻¹ (-1)^{a b}`.
* `hadamardPow n` — the `n`-fold tensor power, indexed by `n`-bit strings `Fin n → Fin 2`,
  defined by the honest block (Kronecker) recursion
  `H^{⊗(n+1)} x y = H (x 0) (y 0) · H^{⊗n} (tail x) (tail y)`. Its faithfulness as *the*
  tensor power is certified by `hadamardPow_apply`, the standard characterisation that a
  Kronecker-power entry is the product of the factor entries: `H^{⊗n} x y = ∏ᵢ H (xᵢ) (yᵢ)`.
* `hadamardPow_apply_eq` — **eq. (2.55)**: `H^{⊗n} x y = (√(2ⁿ))⁻¹ (-1)^{∑ᵢ xᵢ yᵢ}`. This is
  the exercise's main claim, proved (not assumed): the entry is the *product* `∏ᵢ H(xᵢ,yᵢ)`,
  and the closed form drops out of the single-qubit formula by distributing the product.
* `hadamardPow_two_submatrix` — the explicit `4 × 4` matrix for `H^{⊗2}`, in N&C's
  big-endian basis order `00, 01, 10, 11` (given by `bitPair2`).
* `hadamardC` — the same Hadamard `(√2)⁻¹ • !![1, 1; 1, -1]` but with **complex** entries
  (eq. 2.85), the form needed as an *operator* on the qubit's state space `ℂ²`. Its structural
  facts, matching the per-matrix facts of the Pauli file: `hadamardC_isHermitian` (`Hᴴ = H`),
  `hadamardC_mul_self` (`H² = I`, the involution), and `hadamardC_mem_unitaryGroup` — the
  formalisation of **Nielsen & Chuang, Exercise 2.51** (`H` is unitary, `Hᴴ H = I`), a one-line
  consequence of Hermiticity and the involution.

Everything names raw matrix/scalar data only.

## Design notes

* **Index type.** `n`-bit strings are `Fin n → Fin 2`, so an entry of `H^{⊗n}` is indexed by
  a pair of strings and the tensor power is a `Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℝ`.
  This makes the product-of-entries characterisation `∏ᵢ H(xᵢ,yᵢ)` a clean `Finset.prod`
  over `Fin n`, and the dot product `x·y` the natural `∑ᵢ (xᵢ).val (yᵢ).val : ℕ`.
* **Real vs. complex.** N&C's Hadamard has real entries. For the tensor-power identity (2.33) —
  a pure matrix identity with no physical content — `hadamard : Matrix (Fin 2) (Fin 2) ℝ` is
  faithful and keeps the `√2` bookkeeping (`sqrt_two_pow`) on `ℝ` where it is cleanest. The
  qubit gate operators of Chapter 2 act on `EuclideanSpace ℂ (Fin 2)`, so unitarity (2.51) is
  stated for the complex-entried `hadamardC : Matrix (Fin 2) (Fin 2) ℂ`; the two are the same
  matrix over their respective scalar rings (mirroring how the Pauli matrices are kept complex).
* **Unitarity via Hermitian ∧ involution.** `H` is real-symmetric, hence Hermitian, and squares
  to `I`; so `Hᴴ H = H H = I`, which is unitarity.
  This mirrors `pauliX_mem_unitaryGroup` etc. in `CliffordCSS/Gates/Pauli.lean`, and reuses
  `hadamardC_isHermitian` / `hadamardC_mul_self` — the latter is also N&C Exercise 2.52 (`H² = I`).
* **`(-1)^{x·y}` as an integer power.** The exponent `∑ᵢ (xᵢ).val (yᵢ).val` is a genuine `ℕ`
  (not a residue mod 2); since `(-1 : ℝ)` has order `2`, `(-1)^k` depends only on parity, so
  this matches N&C's `(-1)^{x·y}` exactly.
-/

namespace CliffordCSS

open Matrix


/-! ### The complex Hadamard matrix and its unitarity (Nielsen & Chuang, Exercise 2.51)

The Hadamard `H = (1/√2) !![1, 1; 1, -1]` again, now over `ℂ` — the entry ring in which it is
an operator on the qubit's state space `EuclideanSpace ℂ (Fin 2)`. Like each Pauli matrix it is
Hermitian and an involution, and unitarity is the one-line consequence
`Hᴴ H = H H = I`. -/

open Matrix Complex in
/-- The single-qubit Hadamard matrix `H = (1/√2) !![1, 1; 1, -1]` with **complex** entries
(Nielsen & Chuang, eq. 2.85). This is the operator form of `hadamard`, used to build the qubit
Hadamard gate; the two are the same matrix over `ℝ` resp. `ℂ`. -/
noncomputable def hadamardC : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ))⁻¹ • !![1, 1; 1, -1]

/-- The complex Hadamard matrix is Hermitian (`Hᴴ = H`): its entries `±1/√2` are real, and the
matrix is symmetric. -/
theorem hadamardC_isHermitian : hadamardC.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamardC, Matrix.conjTranspose_apply]

/-- The Hadamard normalisation scalar squares to `½`: `(√2)⁻¹ * (√2)⁻¹ = 2⁻¹` over `ℂ`. Shared by
the Hadamard involution and the Hadamard-conjugation lemmas, where the two `(√2)⁻¹` factors of
`H = (√2)⁻¹ !![1,1;1,-1]` combine. -/
theorem inv_sqrt_two_mul_self : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- The Hadamard matrix is an involution: `H² = I`. The scalar `((√2)⁻¹)² = 2⁻¹` combines with
`!![1,1;1,-1]² = 2 • I` to give the identity. (This is also Nielsen & Chuang, Exercise 2.52.) -/
theorem hadamardC_mul_self : hadamardC * hadamardC = 1 := by
  have hc : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ * 2 = 1 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hBB : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) * !![1, 1; 1, -1]
      = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [hadamardC, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBB, smul_smul, hc, one_smul]


end CliffordCSS

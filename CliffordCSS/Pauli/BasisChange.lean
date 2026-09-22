import CliffordCSS.Pauli.String
import CliffordCSS.Gates.HadamardPauliConjugation
import CliffordCSS.Gates.AxisAngleValues
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Local single-qubit basis change reducing `X ⊗ Y ⊗ Z` to `Z ⊗ Z ⊗ Z`

This file is pure mathematics : it supplies the matrix core of
Nielsen & Chuang, **Exercise 4.51** — "construct a quantum circuit to simulate the Hamiltonian
`H = X₁ ⊗ Y₂ ⊗ Z₃`, performing `e^{-iΔt H}` for any `Δt`". Everything here names raw matrix data
only (`Matrix`, `CliffordCSS.pauliString`, `NormedSpace.exp`).lean`.

## The construction (N&C §4.7.3)

N&C's simulation algorithm reduces any tensor-product Pauli Hamiltonian `⊗ₖ σ_{c(k)}` to the
all-`Z` case `Z ⊗ ⋯ ⊗ Z` (whose `e^{-iΔt}` circuit is Figure 4.19, a parity computation into an
ancilla, a conditional phase, and an uncompute) by **single-qubit basis changes**: an `X` or `Y`
factor is conjugated to a `Z` factor by a local unitary. Concretely, with

* `B₁ = H` (Hadamard): `H · Z · Hᴴ = X` (`hadamardC_mul_pauliZ_mul_hadamardC`);
* `B₂ = S·H` (`basisChangeY`): `(SH) · Z · (SH)ᴴ = Y` (`basisChangeY_conj_pauliZ`);
* `B₃ = I`: `I · Z · Iᴴ = Z`,

The local tensor unitary `B = B₁ ⊗ B₂ ⊗ B₃` satisfies `B · (Z ⊗ Z ⊗ Z) · Bᴴ = X ⊗ Y ⊗ Z`, and
hence, for any complex scalar `s` (in the exercise `s = -iΔt`),
`exp(s · (X ⊗ Y ⊗ Z)) = B · exp(s · (Z ⊗ Z ⊗ Z)) · Bᴴ`. Applying `B` locally, running the `Z⊗Z⊗Z`
simulation, and undoing `B` is the circuit for `e^{-iΔt H}`.

## What is proved

* `kronFamily` — the `n`-fold tensor product `⨂ₖ Aₖ` of a family of single-qubit operators,
  defined entrywise `(⨂ₖ Aₖ)(i,j) = ∏ₖ Aₖ(iₖ)(jₖ)` on the register index `Fin n → Fin 2`,
  matching the entrywise form of `pauliString` (so `pauliString g = ⨂ₖ σ_{gₖ}`,
  `pauliString_eq_kronFamily`).
* `kronFamily_mul` — the **mixed-product property** `(⨂ₖ Aₖ)(⨂ₖ Bₖ) = ⨂ₖ (Aₖ Bₖ)`, the
  algebraic engine of the reduction; `kronFamily_conjTranspose` (`(⨂ₖ Aₖ)ᴴ = ⨂ₖ Aₖᴴ`),
  `kronFamily_one` (`⨂ₖ 1 = 1`) and `kronFamily_smul_family` (`⨂ₖ (cₖ • Aₖ) = (∏ₖ cₖ) • ⨂ₖ Aₖ`)
  are its unit/adjoint/scalar companions.
* `basisChangeY` / `sMatrix_conj_pauliX` / `sMatrix_conj_pauliY` / `sMatrix_conj_pauliZ` /
  `basisChangeY_conj_pauliZ` — the `Y` basis-change gate `S·H`, the single-qubit phase-gate tableau
  `S·X·Sᴴ = Y`, `S·Y·Sᴴ = -X`, `S·Z·Sᴴ = Z` (N&C Ex 10.39), and `(SH)·Z·(SH)ᴴ = Y`.
* `pauliString_conj_kronFamily` — the operator identity `B · (Z⊗Z⊗Z) · Bᴴ = X⊗Y⊗Z`, and
* `pauliString_exp_smul_conj_kronFamily` — its exponentiated form `exp(s·(X⊗Y⊗Z)) =
  B · exp(s·(Z⊗Z⊗Z)) · Bᴴ` for any `s : ℂ` (via `Matrix.exp_units_conj`, `B` unitary).
-/

open Matrix Complex

open scoped BigOperators

namespace CliffordCSS

variable {n : ℕ}

/-! ### The `n`-fold tensor product of single-qubit operators -/

/-- The **`n`-fold tensor product** `A₀ ⊗ A₁ ⊗ ⋯ ⊗ A_{n-1}` of a family of single-qubit operators
`A : Fin n → M₂(ℂ)`, as an operator on the `n`-qubit register `Fin n → Fin 2`, defined entrywise by
the product of the per-qubit entries `(⨂ₖ Aₖ)(i,j) = ∏ₖ Aₖ(iₖ)(jₖ)`. This matches the entrywise
form of `pauliString` (`pauliString g = kronFamily (σ_{g·})`, `pauliString_eq_kronFamily`), so the
mixed-product property `kronFamily_mul` conjugates a Pauli string factor-by-factor. -/
def kronFamily (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j => ∏ k, A k (i k) (j k)

@[simp]
theorem kronFamily_apply (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin n → Fin 2) :
    kronFamily A i j = ∏ k, A k (i k) (j k) := rfl

/-- A Pauli string is the tensor product of its per-qubit Pauli factors:
`pauliString g = kronFamily (fun k => pauli (g k))`. Definitional, since both are the entrywise
product `∏ₖ σ_{gₖ}(iₖ)(jₖ)`. -/
theorem pauliString_eq_kronFamily (g : Fin n → Fin 4) :
    pauliString g = kronFamily (fun k => pauli (g k)) := rfl

/-- **Mixed-product property of the tensor product** `(⨂ₖ Aₖ)(⨂ₖ Bₖ) = ⨂ₖ (Aₖ Bₖ)`. The `(i,j)`
entry of the product, `∑_l (∏ₖ Aₖ(iₖ)(lₖ))(∏ₖ Bₖ(lₖ)(jₖ))`, collapses under `Finset.prod_univ_sum`
into `∏ₖ ∑ₐ Aₖ(iₖ)(a) Bₖ(a)(jₖ) = ∏ₖ (Aₖ Bₖ)(iₖ)(jₖ)`: summing over intermediate register states
`l` is choosing an intermediate index per qubit. This is the algebraic engine of the basis-change
reduction (conjugation acts factor-by-factor). -/
theorem kronFamily_mul (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamily A * kronFamily B = kronFamily (fun k => A k * B k) := by
  ext i j
  simp only [kronFamily, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun l _ => Finset.prod_mul_distrib.symm

/-- The conjugate transpose of a tensor product is the tensor product of the conjugate transposes,
`(⨂ₖ Aₖ)ᴴ = ⨂ₖ Aₖᴴ`. Entrywise, `star (∏ₖ Aₖ(jₖ)(iₖ)) = ∏ₖ star (Aₖ(jₖ)(iₖ)) = ∏ₖ Aₖᴴ(iₖ)(jₖ)`
(`map_prod` of the ring conjugation). -/
theorem kronFamily_conjTranspose (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (kronFamily A)ᴴ = kronFamily (fun k => (A k)ᴴ) := by
  ext i j
  rw [Matrix.conjTranspose_apply, kronFamily_apply, kronFamily_apply, ← starRingEnd_apply,
    map_prod]
  exact Finset.prod_congr rfl fun k _ => by rw [starRingEnd_apply, Matrix.conjTranspose_apply]

/-- The tensor product of identities is the identity, `⨂ₖ 1 = 1`. Entrywise
`∏ₖ (if iₖ = jₖ then 1 else 0)` is `1` when `i = j` (every factor `1`) and `0` otherwise (some
qubit factor vanishes). -/
theorem kronFamily_one : kronFamily (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext i j
  simp only [kronFamily_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- Pulling per-qubit scalars out of a tensor product: `⨂ₖ (cₖ • Aₖ) = (∏ₖ cₖ) • ⨂ₖ Aₖ`. Entrywise
the `(i, j)` entry is `∏ₖ cₖ Aₖ(iₖ)(jₖ) = (∏ₖ cₖ)(∏ₖ Aₖ(iₖ)(jₖ))` by `Finset.prod_mul_distrib`. -/
theorem kronFamily_smul_family (c : Fin n → ℂ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    kronFamily (fun k => c k • A k) = (∏ k, c k) • kronFamily A := by
  ext i j
  simp only [kronFamily_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

/-! ### The single-qubit basis-change gates -/


/-- **Phase-gate conjugation** `S·X·Sᴴ = Y` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
rotates `X` into `Y`. A direct `2 × 2` computation. -/
theorem sMatrix_conj_pauliX : sMatrix * pauliX * sMatrixᴴ = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

/-- **Phase-gate conjugation** `S·Y·Sᴴ = -X` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
rotates `Y` into `-X`. A direct `2 × 2` computation. -/
theorem sMatrix_conj_pauliY : sMatrix * pauliY * sMatrixᴴ = -pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]

/-- **Phase-gate conjugation** `S·Z·Sᴴ = Z` (N&C Exercise 10.39): the phase gate `S = diag(1, i)`
fixes `Z`. A direct `2 × 2` computation. -/
theorem sMatrix_conj_pauliZ : sMatrix * pauliZ * sMatrixᴴ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMatrix, pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]


/-! ### The three-qubit basis-change reduction `X ⊗ Y ⊗ Z = B (Z ⊗ Z ⊗ Z) Bᴴ` -/


/-! ### The flat computational-basis (register) indexing `Fin (2ⁿ)` -/


end CliffordCSS

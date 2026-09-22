import CliffordCSS.Gates.Rotation
import CliffordCSS.Gates.Hadamard

/-!
# Axis-angle parameters for the Hadamard and phase gates (Nielsen & Chuang, Ex. 4.8(2,3))

Parts 2 and 3 of **Nielsen & Chuang, Exercise 4.8** ask for the explicit values of `α, θ, n̂` in the
axis-angle decomposition `U = e^{iα} R_n̂(θ)` (eq. 4.9) for two named gates. This file is pure
mathematics : building on the rotation matrices `rotAxis`/`rotZ` of
`CliffordCSS/Gates/Rotation.lean` and the complex Hadamard matrix `hadamardC` of `CliffordCSS/Gates/Hadamard.lean`, it
proves the two `2 × 2` matrix identities that pin those values.

* **Part 2 — the Hadamard gate `H`:** `α = π/2`, `θ = π`, `n̂ = (1/√2, 0, 1/√2)` (the `x̂ + ẑ`
  axis). `hadamardC_eq_expPiDivTwo_smul_rotAxis`:
  `H = e^{iπ/2} • R_{(1/√2, 0, 1/√2)}(π)`.
  At `θ = π` the closed form (`rotAxis_eq_of_unit`) collapses to `-i (n̂·σ)` (since `cos(π/2) = 0`,
  `sin(π/2) = 1`); with this axis `n̂·σ = (1/√2)(X + Z) = H`, and the phase `e^{iπ/2} = i` cancels
  the `-i`, giving `H` exactly.
* **Part 3 — the phase gate `S = diag(1, i)`:** `α = π/4`, `θ = π/2`, `n̂ = ẑ`.
  `sMatrix_eq_expPiDivFour_smul_rotZ`:
  `S = e^{iπ/4} • R_z(π/2)`.
  This is the exact analogue of the π/8 gate identity `T = e^{iπ/8} R_z(π/4)` (`tMatrix`,
  Exercise 4.3): both `S` and `R_z(π/2) = diag(e^{-iπ/4}, e^{iπ/4})` are diagonal, and pulling the
  scalar `e^{iπ/4}` through gives `diag(1, e^{iπ/2}) = diag(1, i) = S`.

Every statement names only raw matrices and real trigonometric constants. The physics reading is
that `H` and `S`, as quantum operations, *are* these rotations, the global phase being
unobservable. -/

namespace CliffordCSS

open Matrix Complex


/-- The **phase gate** `S = diag(1, i)` (Nielsen & Chuang, §4.2), the diagonal single-qubit gate
`!![1, 0; 0, i]`. Written `S = e^{iπ/4} R_z(π/2)` up to a global phase
(`sMatrix_eq_expPiDivFour_smul_rotZ`), the phase-gate analogue of the π/8 gate `tMatrix`. -/
def sMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.I]

/-- **Nielsen & Chuang, Exercise 4.8(3) (phase gate as an axis rotation).** The phase gate equals
`R_z(π/2)` up to the global phase `e^{iπ/4}`: `S = e^{iπ/4} • R_z(π/2)` (so `α = π/4`, `θ = π/2`,
`n̂ = ẑ`). Both are diagonal, and pulling the scalar `e^{iπ/4}` through
`R_z(π/2) = diag(e^{-iπ/4}, e^{iπ/4})` gives `diag(1, e^{iπ/2}) = diag(1, i) = S`, via
`e^{iπ/4}·e^{-iπ/4} = 1` and `e^{iπ/4}·e^{iπ/4} = e^{iπ/2} = i`. -/
theorem sMatrix_eq_expPiDivFour_smul_rotZ :
    sMatrix = Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) • rotZ (Real.pi / 2) := by
  have hI : Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) = Complex.I := by
    exact_mod_cast Complex.exp_pi_div_two_mul_I
  rw [rotZ_eq]
  unfold sMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.smul_apply,
      smul_eq_mul, neg_mul, mul_zero, Complex.ofReal_div, Complex.ofReal_ofNat]
  · -- (0,0): `1 = exp(iπ/4) · exp(-i(π/2)/2)`
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  · -- (1,1): `i = exp(iπ/4) · exp(i(π/2)/2)`, i.e. `exp(iπ/2) = i`
    rw [← Complex.exp_add,
      show (Real.pi : ℂ) / 4 * Complex.I + (Real.pi : ℂ) / 2 / 2 * Complex.I
          = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact hI.symm

/-- The phase gate `S = diag(1, i)` is unitary: it lies in the `2 × 2` unitary group. Immediate from
`S = e^{iπ/4} • R_z(π/2)` (`sMatrix_eq_expPiDivFour_smul_rotZ`), the unitarity of `R_z(π/2)`
(`rotZ_mem_unitaryGroup`), and the fact that scaling a unitary by the unit-modulus phase `e^{iπ/4}`
keeps it unitary. -/
theorem sMatrix_mem_unitaryGroup : sMatrix ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hc : Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) *
      star (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]; norm_num
  rw [sMatrix_eq_expPiDivFour_smul_rotZ, Matrix.mem_unitaryGroup_iff, star_smul,
    smul_mul_smul_comm, Matrix.mem_unitaryGroup_iff.mp (rotZ_mem_unitaryGroup _), hc, one_smul]

end CliffordCSS

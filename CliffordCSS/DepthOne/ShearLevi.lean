import CliffordCSS.Symplectic.Group
import CliffordCSS.ToMathlib.Data.Matrix.CharTwo

/-!
# The depth-one generators — shear circuits `U_Z(S)`, `L_X(T)` and Levi gates
(Beyond transversality, App. B/D.1)

Pure mathematics : the three families of generators of the
fixed-matching generation theorem (Theorem D.1) of *Beyond transversality* (arXiv:2608.05688), as
elements of the binary symplectic group `Sp(2n, 𝔽₂)`. Everything is `𝔽₂` symplectic linear algebra
naming the raw carrier `Matrix`.

## The paper's generators (App. B, Conventions c7/c8)

* **`Z`-diagonal circuit (shear) `U_Z(S) = [[I, S], [0, I]]`** (Convention c7), acting on labels by
  `(a | b) ↦ (a | b + a S)`. It is symplectic **iff** `S` is symmetric (`shearZ_mem_iff`), the
  shears compose additively `U_Z(S) U_Z(S') = U_Z(S + S')` (`shearZ_mul`, so `S ↦ U_Z(S)` is a
  homomorphism of the additive group of matrices into `Sp`), `U_Z(0) = I` (`shearZ_zero`), and over
  `𝔽₂` each shear is its own inverse, `U_Z(S) U_Z(S) = I` (`shearZ_mul_self`, since `S + S = 0`).
* **`X`-diagonal circuit `L_X(T) = [[I, 0], [T, I]]`**, the dual under the `X ↔ Z` swap, acting by
  `(a | b) ↦ (a + b T | b)`; the same four facts hold (`shearX_*`).
* **Levi (linear) gate `Levi(K) = [[K, 0], [0, K⁻ᵀ]]`** for `K ∈ GL(n) = (Matrix n n 𝔽₂)ˣ`
  (Convention c8), acting by `(a | b) ↦ (a K | b K⁻ᵀ)`. It is symplectic for **every** invertible
  `K` (`leviGate_mem`: the off-diagonal symplectic relation is `K K⁻¹ = I`), composes
  `Levi(K) Levi(K') = Levi(K K')` (`leviGate_mul`, a homomorphism `GL(n) → Sp`), and `Levi(1) = I`
  (`leviGate_one`).

These are the atoms of the three generating families `S^Z_M`, `S^X_M`, `L_M` of Theorem D.1. Their
symmetry / block-diagonality / code-preservation constraints (`C_X S ⊆ C_Z`, `M`-block-diagonal,
etc.) — which cut each family down to its valid, matching-supported part inside the two-fold slice
`N_M` — are recorded when those families are assembled as subgroups. Here we only establish the
generators as symplectic-group elements and their group laws.

No orthogonality `C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more".

## What is proved

* `shearZ` / `shearX` / `leviGate` — the three generator matrices.
* `shearZ_mem_iff` / `shearX_mem_iff` — symplectic membership iff the parameter is symmetric.
* `leviGate_mem` — the Levi gate is symplectic for every `K ∈ GL(n)`.
* `shearZ_mul` / `shearX_mul` / `leviGate_mul` — the composition laws (additive for the shears,
  multiplicative for the Levi gates).
* `shearZ_zero` / `shearX_zero` / `leviGate_one` — the identity elements.
* `shearZ_mul_self` / `shearX_mul_self` — the `𝔽₂` involutivity `U_Z(S)² = I`, `L_X(T)² = I`.
* `vecMul_shearZ` / `vecMul_shearX` / `vecMul_leviGate` — the label actions of Conventions c7/c8.
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The `Z`-diagonal circuit (shear) `U_Z(S)` (Convention c7) -/

/-- The **`Z`-diagonal circuit** (shear) `U_Z(S) = [[I, S], [0, I]]` of *Beyond transversality*
(Convention c7): the `2n × 2n` block matrix over `𝔽₂` acting on labels by `(a | b) ↦ (a | b + a S)`
(`vecMul_shearZ`). It is symplectic iff `S` is symmetric (`shearZ_mem_iff`). -/
def shearZ (S : Matrix ι ι (ZMod 2)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  Matrix.fromBlocks 1 S 0 1

/-- The **`X`-diagonal circuit** `L_X(T) = [[I, 0], [T, I]]`, the `X ↔ Z` dual of the `Z`-shear,
acting on labels by `(a | b) ↦ (a + b T | b)` (`vecMul_shearX`). It is symplectic iff `T` is
symmetric (`shearX_mem_iff`). -/
def shearX (T : Matrix ι ι (ZMod 2)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  Matrix.fromBlocks 1 0 T 1

/-- The **Levi (linear) gate** `Levi(K) = [[K, 0], [0, K⁻ᵀ]]` of *Beyond transversality*
(Convention c8), for `K ∈ GL(n) = (Matrix ι ι 𝔽₂)ˣ`: the `2n × 2n` block matrix over `𝔽₂` acting on
labels by `(a | b) ↦ (a K | b K⁻ᵀ)` (`vecMul_leviGate`). `K⁻ᵀ = (K⁻¹)ᵀ` is the inverse-transpose.
Symplectic for every invertible `K` (`leviGate_mem`). -/
def leviGate (K : (Matrix ι ι (ZMod 2))ˣ) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  Matrix.fromBlocks (K : Matrix ι ι (ZMod 2)) 0 0 ((↑K⁻¹ : Matrix ι ι (ZMod 2))ᵀ)

/-! ### Symplectic membership -/

/-- **`U_Z(S)` is symplectic iff `S` is symmetric.** For the shear `[[I, S], [0, I]]` the three
block relations of `fromBlocks_mem_binarySymplecticGroup_iff` reduce to `Sᵀ = S` (the diagonal
relation `A Bᵀ = B Aᵀ`), the other two being `0 = 0` and `I = I`. -/
@[simp] theorem shearZ_mem_iff {S : Matrix ι ι (ZMod 2)} :
    shearZ S ∈ binarySymplecticGroup ι ↔ S.IsSymm := by
  rw [shearZ, fromBlocks_mem_binarySymplecticGroup_iff, Matrix.IsSymm]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_zero,
    Matrix.mul_zero, add_zero, and_true]

/-- **`L_X(T)` is symplectic iff `T` is symmetric.** Dual to `shearZ_mem_iff`: for
`[[I, 0], [T, I]]` the reduced block relation is `C Dᵀ = D Cᵀ`, i.e. `T = Tᵀ`. -/
@[simp] theorem shearX_mem_iff {T : Matrix ι ι (ZMod 2)} :
    shearX T ∈ binarySymplecticGroup ι ↔ T.IsSymm := by
  rw [shearX, fromBlocks_mem_binarySymplecticGroup_iff, Matrix.IsSymm]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, true_and, and_true]
  exact eq_comm


/-! ### Composition laws -/

/-- **Additive composition of `Z`-shears:** `U_Z(S) U_Z(S') = U_Z(S + S')`. Hence `S ↦ U_Z(S)` is a
homomorphism of the additive group of matrices into `Sp(2n, 𝔽₂)`, and `S^Z` is "canonically an
`𝔽₂`-vector space". -/
theorem shearZ_mul (S S' : Matrix ι ι (ZMod 2)) :
    shearZ S * shearZ S' = shearZ (S + S') := by
  rw [shearZ, shearZ, shearZ, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add]
  rw [add_comm]

/-- **Additive composition of `X`-shears:** `L_X(T) L_X(T') = L_X(T + T')`. -/
theorem shearX_mul (T T' : Matrix ι ι (ZMod 2)) :
    shearX T * shearX T' = shearX (T + T') := by
  rw [shearX, shearX, shearX, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add]

/-- **Multiplicative composition of Levi gates:** `Levi(K) Levi(K') = Levi(K K')`. Hence
`K ↦ Levi(K)` is a homomorphism `GL(n) → Sp(2n, 𝔽₂)`. The bottom-right block uses
`(K⁻¹)ᵀ (K'⁻¹)ᵀ = (K'⁻¹ K⁻¹)ᵀ = ((K K')⁻¹)ᵀ`. -/
theorem leviGate_mul (K K' : (Matrix ι ι (ZMod 2))ˣ) :
    leviGate K * leviGate K' = leviGate (K * K') := by
  have hbr : (↑K⁻¹ : Matrix ι ι (ZMod 2))ᵀ * (↑K'⁻¹ : Matrix ι ι (ZMod 2))ᵀ
      = ((↑(K * K')⁻¹ : Matrix ι ι (ZMod 2)))ᵀ := by
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  rw [leviGate, leviGate, leviGate, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← Units.val_mul, hbr]

/-! ### Identity elements and `𝔽₂` involutivity -/

omit [Fintype ι] in
/-- `U_Z(0) = I`: the zero-parameter `Z`-shear is the identity. -/
@[simp] theorem shearZ_zero : shearZ (0 : Matrix ι ι (ZMod 2)) = 1 := by
  rw [shearZ, Matrix.fromBlocks_one]

omit [Fintype ι] in
/-- `L_X(0) = I`: the zero-parameter `X`-shear is the identity. -/
@[simp] theorem shearX_zero : shearX (0 : Matrix ι ι (ZMod 2)) = 1 := by
  rw [shearX, Matrix.fromBlocks_one]

/-- `Levi(1) = I`: the identity linear map gives the identity Levi gate. -/
@[simp] theorem leviGate_one : leviGate (1 : (Matrix ι ι (ZMod 2))ˣ) = 1 := by
  rw [leviGate, inv_one, Units.val_one, Matrix.transpose_one, Matrix.fromBlocks_one]

/-- **`𝔽₂` involutivity of the `Z`-shear:** `U_Z(S) U_Z(S) = I`, since `S + S = 0` over `𝔽₂`.
Together with `shearZ_mem_iff` (for symmetric `S`) this gives `U_Z(S)⁻¹ = U_Z(S)` in the group. -/
theorem shearZ_mul_self (S : Matrix ι ι (ZMod 2)) : shearZ S * shearZ S = 1 := by
  rw [shearZ_mul, Matrix.add_self_eq_zero, shearZ_zero]

/-- **`𝔽₂` involutivity of the `X`-shear:** `L_X(T) L_X(T) = I`. -/
theorem shearX_mul_self (T : Matrix ι ι (ZMod 2)) : shearX T * shearX T = 1 := by
  rw [shearX_mul, Matrix.add_self_eq_zero, shearX_zero]

/-! ### Label actions (Conventions c7/c8, right row action) -/

/-- **Convention c7, the label action of `U_Z(S)`:** `(a | b) ↦ (a | b + a S)`. In the sum
coordinates `Sum.elim a b ᵥ* U_Z(S) = Sum.elim a (a ᵥ* S + b)`. -/
theorem vecMul_shearZ (S : Matrix ι ι (ZMod 2)) (a b : ι → ZMod 2) :
    Matrix.vecMul (Sum.elim a b) (shearZ S) = Sum.elim a (Matrix.vecMul a S + b) := by
  rw [shearZ, vecMul_fromBlocks_blocks]
  simp only [Matrix.vecMul_one, Matrix.vecMul_zero, add_zero]

/-- **The label action of `L_X(T)`:** `(a | b) ↦ (a + b T | b)`. -/
theorem vecMul_shearX (T : Matrix ι ι (ZMod 2)) (a b : ι → ZMod 2) :
    Matrix.vecMul (Sum.elim a b) (shearX T) = Sum.elim (a + Matrix.vecMul b T) b := by
  rw [shearX, vecMul_fromBlocks_blocks]
  simp only [Matrix.vecMul_one, Matrix.vecMul_zero, zero_add]

/-- **Convention c8, the label action of `Levi(K)`:** `(a | b) ↦ (a K | b K⁻ᵀ)`. -/
theorem vecMul_leviGate (K : (Matrix ι ι (ZMod 2))ˣ) (a b : ι → ZMod 2) :
    Matrix.vecMul (Sum.elim a b) (leviGate K)
      = Sum.elim (Matrix.vecMul a (K : Matrix ι ι (ZMod 2)))
          (Matrix.vecMul b ((↑K⁻¹ : Matrix ι ι (ZMod 2))ᵀ)) := by
  rw [leviGate, vecMul_fromBlocks_blocks]
  simp only [Matrix.vecMul_zero, add_zero, zero_add]

end CliffordCSS

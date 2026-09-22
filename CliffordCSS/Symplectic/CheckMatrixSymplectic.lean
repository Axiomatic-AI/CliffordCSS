import CliffordCSS.Encoding.StabilizerGeneratorFlip

/-!
# The symplectic-matrix commutation criterion (Nielsen & Chuang, Exercise 10.33)

This file is pure mathematics : it delivers the **explicit matrix
form** of Nielsen & Chuang, Exercise 10.33 — two Pauli-group elements commute iff the *twisted inner
product* `r(g) Λ r(g′)ᵀ` of their check-matrix rows vanishes mod 2, with the symplectic form `Λ`
written out as the literal block **matrix**. It sits on top of the shared stabilizer infrastructure
(`CliffordCSS/Pauli/Commutation.lean`, `CliffordCSS/Symplectic/CheckMatrix.lean`): the commutation /
anticommutation sign law `pauliString_commute_iff` decides commutation by the *parity* of the
pairing `pauliAnticommCount`; this file re-expresses that pairing as the genuine `Matrix` product
`r(g) Λ r(g′)ᵀ` over `ZMod 2` that the exercise names.

The same mod-2 quantity is already packaged, in `CliffordCSS/Encoding/StabilizerGeneratorFlip.lean`, as the
`LinearMap.BilinForm` `checkSymplectic` (with `checkSymplectic_checkRow : checkSymplectic (checkRow
g) (checkRow h) = (pauliAnticommCount g h : ZMod 2)`), used there for the nondegeneracy argument of
Proposition 10.4. That bilinear form does **not** expose `Λ` as a `Matrix`; this file adds exactly
that literal-`Matrix` presentation `symplecticMatrix = [[0, I], [I, 0]]` and connects the two
(`symplecticForm_checkVec_eq_checkSymplectic`), so the library's two symplectic-form treatments are
linked rather than parallel — the matrix bridge `symplecticForm_checkVec` is *derived from*
`checkSymplectic_checkRow`, not re-proved.

Everything here names only raw matrix / index data (`Matrix`, `CliffordCSS.pauliString`,
`CliffordCSS.checkRow`, `Fin n → Fin 4`, `ZMod 2`).

## The `2n`-vector `r(g)` and the symplectic matrix `Λ`

N&C represents an `n`-qubit Pauli operator `g` by a **`2n`-dimensional row vector** `r(g) = (x_g |
z_g)` over `ZMod 2` — its `X`-part and `Z`-part concatenated — and defines the `2n × 2n` matrix

`Λ = [[0, I], [I, 0]]` (eq. (10.84))

With `n × n` identity blocks on the off-diagonal. We index the `2n` coordinates by `Fin n ⊕ Fin n`
(canonically `≃ Fin (2n)`), so that:

* `checkVec g : Fin n ⊕ Fin n → ZMod 2` is `r(g)`, the `X`-bit on the `inl` block and the `Z`-bit on
  the `inr` block — the flat form of the split `checkRow g` of `CliffordCSS/Symplectic/CheckMatrix.lean`;
* `symplecticMatrix : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)` is `Λ`, written literally as
  `Matrix.fromBlocks 0 1 1 0` (the block structure is exactly the `Fin n ⊕ Fin n` decomposition);
* `symplecticForm x y = x ⬝ᵥ Λ.mulVec y` is the *twisted inner product* `x Λ yᵀ` (row `×` matrix `×`
  column), so `symplecticForm (checkVec g) (checkVec h)` is `r(g) Λ r(h)ᵀ`.

## What is proved

* `symplecticForm_checkVec_eq_checkSymplectic` — the `Matrix`-level twisted product **is the
  existing bilinear form**: `r(g) Λ r(h)ᵀ = checkSymplectic (checkRow g) (checkRow h)`. Since
  `Λ = [[0,I],[I,0]]` swaps the `X`- and `Z`-blocks (`Matrix.fromBlocks_mulVec`), both sides are
  `Σ_k (x_{g,k} z_{h,k} + z_{g,k} x_{h,k})`. This links the two symplectic-form treatments.
* `symplecticForm_checkVec` — the bridge to the parity engine, `r(g) Λ r(h)ᵀ =
  (pauliAnticommCount g h : ZMod 2)`, obtained by composing the equality above with the existing
  `checkSymplectic_checkRow` (no re-expansion of the per-qubit sum).
* `pauliString_commute_iff_symplecticForm` — **Nielsen & Chuang, Exercise 10.33** in its matrix
  form: `Commute P_g P_h ↔ r(g) Λ r(h)ᵀ = 0`. Combines the parity criterion
  `pauliString_commute_iff` (`Commute ↔ Even (pauliAnticommCount g h)`) with the bridge
  `symplecticForm_checkVec` and the `ZMod 2` reading `Even m ↔ (m : ZMod 2) = 0`
  (`CharP.cast_eq_zero_iff`).
* `checkVec_pauliMulIndex` — **the homomorphism law in flat form**: `r(g ⊙ h) = r(g) + r(h)`, the
  `Fin n ⊕ Fin n`-indexed restatement of `checkRow_pauliMulIndex`.
* `vecPauli` / `checkVec_vecPauli` / `vecPauli_checkVec` — the Pauli string with a prescribed check
  vector, and the two round-trips making it a two-sided inverse of `checkVec` (the flat counterpart
  of `checkRow_surjective`, qubitwise `bitToPauli`).
* `checkVecEquiv` — those packaged as **the label bijection**
  `(Fin n → Fin 4) ≃ (Fin n ⊕ Fin n → ZMod 2)`: a phase-free Pauli string *is* its `(x | z)` label.
* `vecPauli_add` — the inverse homomorphism law, `vecPauli (u + v) = vecPauli u ⊙ vecPauli v`, so
  the bijection carries `𝔽₂^{2n}` addition to the Pauli-index product.

## Design notes

* The `2n` index is `Fin n ⊕ Fin n` rather than `Fin (2n)`: this makes N&C's block matrix
  `Λ = [[0, I], [I, 0]]` literal (`Matrix.fromBlocks`) and the `(x | z)` split of `r(g)` a
  `Sum.elim`, keeping the multiplication `Λ · r(h)` a single `Matrix.fromBlocks_mulVec` rewrite. The
  ordering "first `n` coordinates = `X`-part, last `n` = `Z`-part" is exactly N&C's convention.
* Reuse over re-proof: the underlying `ZMod 2` value is the pre-existing `checkSymplectic`; this
  file contributes only the literal-`Matrix` presentation of `Λ` (absent from the `BilinForm`)
  and its identification with `checkSymplectic`, so the matrix bridge to `pauliAnticommCount`
  reduces to the already-proved `checkSymplectic_checkRow`.
-/

open Matrix

open scoped BigOperators

namespace CliffordCSS

variable {n : ℕ}

/-- The `2n`-dimensional **check-matrix row** `r(g) = (x_g | z_g)` of a Pauli string as a single
flat vector over `Fin n ⊕ Fin n` and `ZMod 2` (Nielsen & Chuang §10.5.1): the `inl k` coordinate is
the `X`-bit and the `inr k` coordinate the `Z`-bit of the `k`-th single-qubit Pauli `g k`. Its two
blocks are the components of the split `checkRow g` (`CliffordCSS/Symplectic/CheckMatrix.lean`); the flat form is
`2n`-vector N&C writes `r(g)`, ready to pair with the symplectic matrix `Λ`. -/
def checkVec (g : Fin n → Fin 4) : Fin n ⊕ Fin n → ZMod 2 :=
  Sum.elim (checkRow g).1 (checkRow g).2

@[simp]
theorem checkVec_inl (g : Fin n → Fin 4) (k : Fin n) :
    checkVec g (Sum.inl k) = (pauliBit (g k)).1 := rfl

@[simp]
theorem checkVec_inr (g : Fin n → Fin 4) (k : Fin n) :
    checkVec g (Sum.inr k) = (pauliBit (g k)).2 := rfl

/-- **The check vector is a homomorphism** (flat form): `r(g ⊙ h) = r(g) + r(h)`, the flat-vector
restatement of `checkRow_pauliMulIndex`; componentwise it is `pauliBit_pauliMul`. -/
theorem checkVec_pauliMulIndex (g h : Fin n → Fin 4) :
    checkVec (pauliMulIndex g h) = checkVec g + checkVec h := by
  ext s; cases s <;> simp [checkVec, checkRow, pauliMulIndex, pauliBit_pauliMul]

/-! ### The label bijection: Pauli strings modulo phase `≃ 𝔽₂^{2n}` -/

/-- The **Pauli string with a prescribed check vector**: `vecPauli v` puts on wire `k` the Pauli
with `X`-bit `v (inl k)` and `Z`-bit `v (inr k)` (qubitwise `bitToPauli`). It is the two-sided
inverse of `checkVec` (`checkVec_vecPauli`, `vecPauli_checkVec`), packaged as `checkVecEquiv`. -/
def vecPauli (v : Fin n ⊕ Fin n → ZMod 2) : Fin n → Fin 4 :=
  fun k => bitToPauli (v (Sum.inl k), v (Sum.inr k))

/-- `vecPauli` is a **right** inverse of `checkVec`: every `2n`-bit label is the check vector of a
Pauli string, `checkVec (vecPauli v) = v`. The flat `Fin n ⊕ Fin n`-indexed counterpart of
`checkRow_surjective`. -/
@[simp]
theorem checkVec_vecPauli (v : Fin n ⊕ Fin n → ZMod 2) : checkVec (vecPauli v) = v := by
  funext i
  cases i with
  | inl k => simpa [vecPauli] using congrArg Prod.fst (pauliBit_bitToPauli (v (.inl k), v (.inr k)))
  | inr k => simpa [vecPauli] using congrArg Prod.snd (pauliBit_bitToPauli (v (.inl k), v (.inr k)))

/-- `vecPauli` is a **left** inverse of `checkVec`: a Pauli string is recovered from its label,
`vecPauli (checkVec g) = g` — the faithfulness of the symplectic representation, qubitwise
`bitToPauli_pauliBit`. -/
@[simp]
theorem vecPauli_checkVec (g : Fin n → Fin 4) : vecPauli (checkVec g) = g := by
  funext k
  simpa [vecPauli] using bitToPauli_pauliBit (g k)

/-- **The label bijection** `r : {Pauli strings} ≃ 𝔽₂^{2n}` of Nielsen & Chuang §10.5.1: a
phase-free `n`-qubit Pauli string is the same thing as its `2n`-bit check vector `(x | z)`. Bundles
`checkVec` with its inverse `vecPauli`. It is additive in the sense that it carries the Pauli-index
product to addition (`checkVec_pauliMulIndex`, `vecPauli_add`). -/
def checkVecEquiv : (Fin n → Fin 4) ≃ (Fin n ⊕ Fin n → ZMod 2) where
  toFun := checkVec
  invFun := vecPauli
  left_inv := vecPauli_checkVec
  right_inv := checkVec_vecPauli

@[simp] theorem checkVecEquiv_apply (g : Fin n → Fin 4) : checkVecEquiv g = checkVec g := rfl

@[simp] theorem checkVecEquiv_symm_apply (v : Fin n ⊕ Fin n → ZMod 2) :
    checkVecEquiv.symm v = vecPauli v := rfl

/-- **Adding labels multiplies Paulis**: `vecPauli (u + v) = vecPauli u ⊙ vecPauli v`, the inverse
form of `checkVec_pauliMulIndex`; qubitwise it is `bitToPauli_add`. -/
theorem vecPauli_add (u v : Fin n ⊕ Fin n → ZMod 2) :
    vecPauli (u + v) = pauliMulIndex (vecPauli u) (vecPauli v) := by
  funext k
  exact bitToPauli_add (u (.inl k), u (.inr k)) (v (.inl k), v (.inr k))

/-- The **symplectic form matrix** `Λ = [[0, I], [I, 0]]` (Nielsen & Chuang eq. (10.84)), the
`2N × 2N` matrix over `ZMod 2` with `N × N` zero blocks on the diagonal and identity blocks on the
off-diagonal, written literally as `Matrix.fromBlocks 0 1 1 0` on the `ι ⊕ ι` decomposition of the
`2N` coordinates (`N = |ι|`). It exchanges the `X`- and `Z`-halves of a check vector, encoding the
`(x | z) ↦ (z | x)` swap at the heart of the "twisted" inner product. The index `ι` is left general
(the Pauli-string case is `ι = Fin n`) so the *same* `Λ` serves any block-partitioned coordinate
set, e.g. the standard-form columns `Fin r ⊕ Fin m ⊕ Fin k` of Exercises 10.53–10.54. -/
def symplecticMatrix {ι : Type*} [DecidableEq ι] : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  Matrix.fromBlocks 0 1 1 0

/-- The **twisted inner product** `x Λ yᵀ = x ⬝ᵥ (Λ · y)` of two `2N`-vectors over `ZMod 2`
(Nielsen & Chuang §10.5.1: "the formula `x Λ yᵀ` defines a sort of 'twisted' inner product between
row matrices `x` and `y`"). Applied to two check rows, `symplecticForm (checkVec g) (checkVec h)` is
exactly `r(g) Λ r(h)ᵀ`, whose vanishing mod 2 is Exercise 10.33's commutation criterion. It is the
`Matrix`-level presentation of the bilinear form `checkSymplectic`
(`symplecticForm_checkVec_eq_checkSymplectic`). The coordinate index `ι` is general, so this single
definition serves both the Pauli-string check rows (`ι = Fin n`) and the standard-form rows of
Exercises 10.53–10.54 (`ι = Fin r ⊕ Fin m ⊕ Fin k`). -/
def symplecticForm {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι ⊕ ι → ZMod 2) : ZMod 2 :=
  x ⬝ᵥ symplecticMatrix.mulVec y

/-- **The twisted inner product in expanded form**: `symplecticForm x y = xₓ · z_y + z_x · yₓ`,
where `xₓ = x ∘ inl` is the `X`-part and `z_x = x ∘ inr` the `Z`-part (Nielsen & Chuang's `x Λ yᵀ`
with `Λ = [[0, I], [I, 0]]` swapping the halves). This is the `Λ`-free presentation used in
computations; it holds for any coordinate index `ι`. -/
theorem symplecticForm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι ⊕ ι → ZMod 2) :
    symplecticForm x y = (x ∘ Sum.inl) ⬝ᵥ (y ∘ Sum.inr) + (x ∘ Sum.inr) ⬝ᵥ (y ∘ Sum.inl) := by
  have hΛ : symplecticMatrix.mulVec y = Sum.elim (y ∘ Sum.inr) (y ∘ Sum.inl) := by
    rw [symplecticMatrix, Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
  rw [symplecticForm, hΛ]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]

/-- **The `Matrix`-level twisted product of two check rows is the bilinear form `checkSymplectic`**:
`r(g) Λ r(h)ᵀ = checkSymplectic (checkRow g) (checkRow h)`. Since `Λ = [[0, I], [I, 0]]` swaps the
`X`- and `Z`-blocks (`Matrix.fromBlocks_mulVec`), the matrix product `r(g) Λ r(h)ᵀ` is `Σ_k (x_{g,k}
z_{h,k} + z_{g,k} x_{h,k})`, which is exactly `checkSymplectic` evaluated on the two rows
(`checkSymplectic_apply`). This identifies the explicit-`Matrix` presentation of Exercise 10.33 with
the pre-existing `LinearMap.BilinForm` treatment (`CliffordCSS/Encoding/StabilizerGeneratorFlip.lean`). -/
theorem symplecticForm_checkVec_eq_checkSymplectic (g h : Fin n → Fin 4) :
    symplecticForm (checkVec g) (checkVec h) = checkSymplectic (checkRow g) (checkRow h) := by
  have hΛ : symplecticMatrix.mulVec (checkVec h) = Sum.elim (checkRow h).2 (checkRow h).1 := by
    rw [symplecticMatrix, Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
    rfl
  rw [symplecticForm, hΛ, checkSymplectic_apply]
  simp only [dotProduct, Fintype.sum_sum_type]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [checkVec, Sum.elim_inl, Sum.elim_inr]

/-- **The twisted inner product of two check rows equals the mod-2 symplectic pairing**:
`r(g) Λ r(h)ᵀ = (pauliAnticommCount g h : ZMod 2)`. Immediate from the identification with the
bilinear form (`symplecticForm_checkVec_eq_checkSymplectic`) and the existing bridge
`checkSymplectic_checkRow`. This is what turns the parity criterion `pauliString_commute_iff` into
the matrix form of Exercise 10.33. -/
theorem symplecticForm_checkVec (g h : Fin n → Fin 4) :
    symplecticForm (checkVec g) (checkVec h) = (pauliAnticommCount g h : ZMod 2) := by
  rw [symplecticForm_checkVec_eq_checkSymplectic, checkSymplectic_checkRow]


end CliffordCSS

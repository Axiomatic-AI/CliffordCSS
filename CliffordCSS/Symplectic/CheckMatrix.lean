import CliffordCSS.Pauli.Commutation
import Mathlib.Data.ZMod.Basic

/-!
# The check-matrix row of a Pauli string is an additive homomorphism

This file is pure mathematics : it formalizes the algebraic core of
Nielsen & Chuang's **check-matrix representation** of the Pauli group (N&C §10.5.1, the paragraph
preceding eq. (10.83) and the proof of Proposition 10.3). The check matrix records, for a Pauli
operator `g`, its `2n`-bit **row** `r(g) = (x_g | z_g)` — a `1` in the `k`-th `X`-slot when `g` has
an `X` (or `Y`) on qubit `k`, a `1` in the `k`-th `Z`-slot when `g` has a `Z` (or `Y`). The central
fact N&C uses is that this row map is a **homomorphism modulo phase**:

> `r(g) + r(g′) = r(g g′)`, so addition in the row representation corresponds to multiplication of
> group elements,

Together with its **trivial kernel** — a Pauli string is the identity exactly when its row vanishes.
These are exactly the two ingredients of the Proposition 10.3 proof ("independent generators iff the
check-matrix rows are linearly independent"); they are also shared infrastructure for Propositions
10.4 and 10.5.

Everything here names only raw matrix / index data (`Matrix`, `CliffordCSS.pauli`, `CliffordCSS.
pauliString`, `Fin n → Fin 4`, `ZMod 2`).

## The Pauli-index product and its phase

Two single-qubit Pauli matrices multiply to a third **up to a phase** `±1, ±i`: `σ_a σ_b = ζ(a,b)
σ_{a⊙b}`. The **product index** `a ⊙ b` (`pauliMul`) is the bitwise XOR of the `(x, z)` bit
representations (`I = (0,0)`, `X = (1,0)`, `Y = (1,1)`, `Z = (0,1)`), and `ζ(a,b)` (`pauliMulPhase`)
is the fourth-root-of-unity phase. Lifting factor-by-factor over the `n`-fold tensor product
(`kronFamily`) gives the `n`-qubit product law `P_g P_h = (∏_k ζ(g_k, h_k)) · P_{g ⊙ h}`
(`pauliString_mul_eq_smul`), so the product of two Pauli strings is again a phase times a Pauli
string — the closure fact behind the Pauli group.

## What is proved

* `pauliMul` / `pauliMulPhase` — the Pauli-index product table and its phase table.
* `pauli_mul_eq_smul_pauliMul` — the single-qubit product law `σ_a σ_b = ζ(a,b) σ_{a⊙b}` (a finite
  `4 × 4` case check).
* `pauliMulIndex` / `pauliString_mul_eq_smul` — the `n`-qubit product law `P_g P_h =
  (∏_k ζ(g_k, h_k)) · P_{g ⊙ h}`, obtained factor-by-factor via `kronFamily_mul` and
  `kronFamily_smul_family`.
* `pauliBit` / `checkRow` — the single-qubit `(x, z)` bit pair and the `n`-qubit check-matrix row
  `r(g) = (x_g | z_g) : (Fin n → ZMod 2) × (Fin n → ZMod 2)`.
* `checkRow_pauliMulIndex` — **the homomorphism law** `r(g ⊙ h) = r(g) + r(h)` (mod 2); since
  `P_g P_h` is a phase times `P_{g ⊙ h}`, this is N&C's `r(g g′) = r(g) + r(g′)`.
* `checkRow_eq_zero_iff` — **the trivial kernel** `r(g) = 0 ↔ g = 0` (all-identity string).

The general facts `pauliString_injective` (distinct indices give distinct operators) and
`pauliString_eq_one_iff` (`P_g = I ↔ g = 0`), which the trivial kernel combines with to give
`P_g = I ↔ r(g) = 0`, live with the `pauliString` family in `CliffordCSS/Pauli/String.lean`.

## Design notes

* The check row is valued in `(Fin n → ZMod 2) × (Fin n → ZMod 2)` (the `X`-part and `Z`-part), an
  `F₂`-vector space, so "the rows are linearly independent" (Proposition 10.3) is
  `LinearIndependent (ZMod 2)` of the family of rows. The single-qubit bit pair `pauliBit` reuses
  the natural-number bits `pauliXBit`, `pauliZBit` (`CliffordCSS/Pauli/Commutation.lean`) reduced
  mod 2 — one source of truth for the `(x | z)` convention. Since `pauliMul` is exactly their XOR,
  the homomorphism law `pauliBit (pauliMul a b) = pauliBit a + pauliBit b` is a `16`-case `decide`.
* The phase `pauliMulPhase` is recorded explicitly (a fourth root of unity) even though Proposition
  10.3 only needs it to be a nonzero scalar; the exact table is what makes `P_g P_h` land back in
  the Pauli group and is reused by the Pauli-group closure development.
-/

open Matrix Complex

open scoped BigOperators

namespace CliffordCSS

/-! ### The single-qubit Pauli-index product and its phase -/

/-- The **Pauli-index product** `a ⊙ b`: the index of the Pauli matrix `σ_a σ_b` up to phase. It is
the bitwise XOR of the `(x, z)` bit representations `I = (0,0)`, `X = (1,0)`, `Y = (1,1)`,
`Z = (0,1)` (e.g. `X ⊙ Y = Z`, `Y ⊙ Z = X`). -/
def pauliMul : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]]

/-- The **phase** `ζ(a, b)` in the single-qubit product `σ_a σ_b = ζ(a,b) σ_{a⊙b}`, a fourth root of
unity: `1` when the two Paulis commute in the naive sense (equal, or one is `I`), `±i` otherwise
(e.g. `X Y = i Z`, `Y X = -i Z`). -/
def pauliMulPhase : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, I, -I], ![1, -I, 1, I], ![1, I, -I, 1]]

/-- **Single-qubit Pauli product law**: `σ_a σ_b = ζ(a,b) · σ_{a⊙b}`. Two single-qubit Paulis
multiply to a third up to a fourth-root-of-unity phase; the product index is `pauliMul` and the
phase is `pauliMulPhase`. Proved by the finite `4 × 4` case check on `a, b`. -/
theorem pauli_mul_eq_smul_pauliMul (a b : Fin 4) :
    pauli a * pauli b = pauliMulPhase a b • pauli (pauliMul a b) := by
  fin_cases a <;> fin_cases b <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [pauliMul, pauliMulPhase, pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
        Fin.sum_univ_two])

/-! ### The `n`-qubit Pauli-string product law -/

variable {n : ℕ}

/-- The **`n`-qubit product index** `g ⊙ h`, the componentwise Pauli-index product `k ↦ (g k) ⊙
(h k)`. It is the index of the Pauli string `P_g P_h` up to phase (`pauliString_mul_eq_smul`). -/
def pauliMulIndex (g h : Fin n → Fin 4) : Fin n → Fin 4 := fun k => pauliMul (g k) (h k)

/-- **The `n`-qubit Pauli-string product law**: `P_g P_h = (∏_k ζ(g_k, h_k)) · P_{g ⊙ h}`. The
product of two Pauli strings is a phase times the Pauli string of the product index. Obtained
factor-by-factor from the single-qubit law (`pauli_mul_eq_smul_pauliMul`) via the tensor
mixed-product property (`kronFamily_mul`) and the per-qubit scalar pull-out
(`kronFamily_smul_family`): each qubit contributes its phase `ζ(g_k, h_k)`, and the phases multiply
to `∏_k ζ(g_k, h_k)`. This is the closure fact behind the Pauli group. -/
theorem pauliString_mul_eq_smul (g h : Fin n → Fin 4) :
    pauliString g * pauliString h =
      (∏ k, pauliMulPhase (g k) (h k)) • pauliString (pauliMulIndex g h) := by
  rw [pauliString_eq_kronFamily g, pauliString_eq_kronFamily h, kronFamily_mul]
  simp only [pauli_mul_eq_smul_pauliMul]
  rw [kronFamily_smul_family, pauliString_eq_kronFamily]
  rfl


/-! ### The check-matrix row and its homomorphism law -/

/-- The **single-qubit check bits** `(x_a, z_a)` of a Pauli index: `I = (0,0)`, `X = (1,0)`,
`Y = (1,1)`, `Z = (0,1)`. This is the `(x | z)` symplectic representation over `ZMod 2`; it reuses
the single source of truth for the bit assignment, the natural-number bits `pauliXBit`, `pauliZBit`
of `CliffordCSS/Pauli/Commutation.lean` (`x`-bit `1` for the Paulis containing an `X` factor
`X`, `Y`; `z`-bit `1` for those containing a `Z` factor `Y`, `Z`), reduced mod 2. -/
def pauliBit : Fin 4 → ZMod 2 × ZMod 2 := fun a => ((pauliXBit a : ZMod 2), (pauliZBit a : ZMod 2))

/-- The check bits vanish exactly for the identity Pauli: `pauliBit a = 0 ↔ a = 0`. Only `σ₀ = I`
has both `x`- and `z`-bit `0`. -/
theorem pauliBit_eq_zero_iff (a : Fin 4) : pauliBit a = 0 ↔ a = 0 := by
  fin_cases a <;> decide

/-- The check bits are **additive under the Pauli-index product**: `pauliBit (a ⊙ b) = pauliBit a +
pauliBit b` (mod 2). This is the single-qubit homomorphism law; it holds because `pauliMul` is the
XOR of the bit representations. A finite `4 × 4` case check. -/
theorem pauliBit_pauliMul (a b : Fin 4) : pauliBit (pauliMul a b) = pauliBit a + pauliBit b := by
  fin_cases a <;> fin_cases b <;> decide

/-- The **`n`-qubit check-matrix row** `r(g) = (x_g | z_g)` of a Pauli string, its `X`-part and
`Z`-part over `ZMod 2`: `x_g k`, `z_g k` are the check bits of the `k`-th single-qubit Pauli `g k`.
This is the `2n`-bit row that Nielsen & Chuang assigns to a stabilizer generator; the family of rows
of a generating set is the check matrix. -/
def checkRow (g : Fin n → Fin 4) : (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun k => (pauliBit (g k)).1, fun k => (pauliBit (g k)).2)

/-- **The check-matrix homomorphism law** (Nielsen & Chuang §10.5.1): `r(g ⊙ h) = r(g) + r(h)`
(mod 2). Since `P_g P_h = (phase) · P_{g ⊙ h}` (`pauliString_mul_eq_smul`), this is N&C's
`r(g g′) = r(g) + r(g′)` — "addition in the row representation corresponds to multiplication of
group elements". Componentwise it is the single-qubit additivity `pauliBit_pauliMul`. -/
theorem checkRow_pauliMulIndex (g h : Fin n → Fin 4) :
    checkRow (pauliMulIndex g h) = checkRow g + checkRow h := by
  ext k <;>
    simp only [checkRow, pauliMulIndex, Prod.fst_add, Prod.snd_add, Pi.add_apply, pauliBit_pauliMul]

/-- **The check row has trivial kernel**: `r(g) = 0 ↔ g = 0`, i.e. a Pauli string's row vanishes
exactly when it is the all-identity string. Componentwise, both check bits vanish iff each
single-qubit Pauli is `I` (`pauliBit_eq_zero_iff`). -/
theorem checkRow_eq_zero_iff (g : Fin n → Fin 4) : checkRow g = 0 ↔ g = 0 := by
  simp [checkRow, Prod.ext_iff, funext_iff, ← pauliBit_eq_zero_iff, forall_and]


end CliffordCSS

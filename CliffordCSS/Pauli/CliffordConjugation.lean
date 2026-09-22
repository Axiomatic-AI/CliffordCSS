import CliffordCSS.Symplectic.CheckMatrix

/-!
# Single-wire Clifford conjugation of Pauli strings and check-matrix column operations

This file is pure mathematics : it establishes how the **single-wire
Clifford generators** — the Hadamard gate `H` and the phase gate `S` placed on one qubit of an
`n`-qubit register — act on a Pauli string (`CliffordCSS.pauliString`, `g : Fin n → Fin 4`) by
**conjugation**, and how that conjugation acts on the string's **binary symplectic check-matrix**
row (the `(x | z)` bits `pauliXBit`, `pauliZBit` of `CliffordCSS/Pauli/Commutation.lean`).
Conjugating a Pauli string by a Clifford gate returns another Pauli string (up to a `±1` phase), and
on the check matrix this is exactly an **elementary symplectic column operation**:

* **Hadamard on wire `j`** swaps the `X`-bit and `Z`-bit of column `j` (`H` exchanges the `x̂`/`ẑ`
  Bloch axes): `x_j ↔ z_j`.
* **Phase `S` on wire `j`** adds the `X`-bit into the `Z`-bit of column `j` (mod 2):
  `z_j ↦ z_j + x_j`.

This is the algebraic engine of the *encoding circuit* of Nielsen & Chuang **Problem 10.3**: a
Clifford circuit acts on the `n × 2n` check matrix of a stabilizer code by column operations, and
the encoding circuit is a sequence of such operations taking the trivial check matrix `[0 | I]`
(Eq. 10.124) to the standard form (Eq. 10.125). The single-wire generators formalised here are the
`H`/`S` half of that gate set (the two-wire generator `CNOT` is a separate development); more
broadly they are shared infrastructure for the whole Chapter-10 stabilizer program (Gottesman–Knill
Thm 10.7, the Clifford normalizer Thm 10.6, Ex 10.39).

Everything names only raw matrix / index data (`Matrix`, `CliffordCSS.pauli`, `CliffordCSS.pauliString`,
`CliffordCSS.kronFamily`, `Fin n → Fin 4`).

## The gate on a wire

`kronWireGate j G = kronFamily (Function.update (fun _ => 1) j G)` places the single-qubit gate `G`
on wire `j` of the register `Fin n → Fin 2` (identity on every other wire), `I ⊗ ⋯ ⊗ G ⊗ ⋯ ⊗ I`.
When `G` is unitary so is `kronWireGate j G` (`kronWireGate_mul_conjTranspose`,
`kronWireGate_conjTranspose_mul`), so it is a genuine one-qubit gate of a circuit.

## What is proved

* `hadamardC_conj_pauli` / `sMatrix_conj_pauli` — the **single-qubit tableaux**
  `H σ_a H† = ε_H(a) • σ_{H·a}` and `S σ_a S† = ε_S(a) • σ_{S·a}`, where the index maps
  `hadamardPauli` (`I,X,Y,Z ↦ I,Z,Y,X`) / `phasePauli` (`I,X,Y,Z ↦ I,Y,X,Z`) and the signs
  `hadamardPauliSign` / `phasePauliSign` record the Clifford action `H X H=Z`, `H Y H=-Y`, `H Z H=X`
  and `S X S†=Y`, `S Y S†=-X`, `S Z S†=Z` on the single qubit. (`S X S† = Y` is N&C Exercise 10.39.)
* `kronWireGate_conj_pauliString` — the **`n`-qubit lift**: for any single-qubit gate `G` with
  tableau `G σ_a G† = ε a • σ_{τ a}`, conjugating a Pauli string by `kronWireGate j G` rewrites only
  wire `j`:
  `kronWireGate j G · P_g · (kronWireGate j G)† = ε (g j) • P_{update g j (τ (g j))}`. Proved
  factor-by-factor by the mixed-product property `kronFamily_mul` (only the `j`-th factor is not
  `1 · σ · 1 = σ`), with the single non-trivial sign pulled out by `kronFamily_smul_family` (all
  other wires contribute the scalar `1`, `Finset.prod_update_of_mem`).
* `hadamardWire_conj_pauliString` / `phaseWire_conj_pauliString` — the two instances (`G = H`, `S`).
* `pauliXBit_hadamardPauli` / `pauliZBit_hadamardPauli` (the `H` column op `x_j ↔ z_j`) and
  `pauliXBit_phasePauli` / `pauliZBit_phasePauli` (the `S` column op `z_j ↦ z_j + x_j (mod 2)`) —
  the symplectic **check-matrix column operations** these gates induce.

## Design notes

* The carrier is the **phase-free** `pauliString`; the `±1` acquired under conjugation is tracked
  explicitly as the scalar `ε`, matching the sign law `pauliString_mul_comm_sign` of the commutation
  file. The check-matrix bit maps `hadamardPauli`/`phasePauli` discard the sign (the check matrix is
  a phase-free `(x | z)` record), which is why the encoding-circuit column operations are stated on
  the bits alone.
* Both single-qubit tableaux are finite `Fin 4` case checks citing the per-Pauli conjugation
  lemmas: the Hadamard tableau cites `hadamardC_mul_pauli{X,Y,Z}_mul_hadamardC`, the phase tableau
  cites `sMatrix_conj_pauli{X,Y,Z}` (all in `CliffordCSS/Pauli/BasisChange.lean`, the `Y`/`Z`
  siblings extracted next to the pre-existing `sMatrix_conj_pauliX`), plus `S S† = 1` for the `I`
  case.
* The lift `kronWireGate_conj_pauliString` is the same `kronFamily` factor-by-factor idiom as
  `pauliString_conj_kronFamily` (Exercise 4.51), specialised to a gate supported on a single wire
  via `Function.update`.
-/

open Matrix

open scoped BigOperators

namespace CliffordCSS

variable {n : ℕ}

/-! ### The single-qubit Clifford tableaux -/

/-- The **Hadamard tableau** on a Pauli index: `I, X, Y, Z ↦ I, Z, Y, X` (`0,1,2,3 ↦ 0,3,2,1`). It
records the Pauli that `H σ_a H` produces, up to sign (`hadamardPauliSign`): `H` exchanges the `x̂`
and `ẑ` Bloch axes and fixes `ŷ`. On the binary symplectic bits this is the swap `(x, z) ↦ (z, x)`
(`pauliXBit_hadamardPauli`, `pauliZBit_hadamardPauli`). -/
def hadamardPauli : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- The **sign** in the Hadamard tableau `H σ_a H = hadamardPauliSign a • σ_{hadamardPauli a}`: `-1`
for `a = Y` (since `H Y H = -Y`) and `+1` otherwise. -/
def hadamardPauliSign : Fin 4 → ℂ := ![1, 1, -1, 1]

/-- The **phase-gate tableau** on a Pauli index: `I, X, Y, Z ↦ I, Y, X, Z` (`0,1,2,3 ↦ 0,2,1,3`). It
records the Pauli that `S σ_a S†` produces, up to sign (`phasePauliSign`): the phase gate
`S = diag(1, i)` rotates `X ↦ Y` and `Y ↦ X` and fixes `Z`. On the binary symplectic bits this is
`(x, z) ↦ (x, z + x mod 2)` (`pauliXBit_phasePauli`, `pauliZBit_phasePauli`). -/
def phasePauli : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- The **sign** in the phase-gate tableau `S σ_a S† = phasePauliSign a • σ_{phasePauli a}`: `-1`
for `a = Y` (since `S Y S† = -X`) and `+1` otherwise. -/
def phasePauliSign : Fin 4 → ℂ := ![1, 1, -1, 1]

/-- **Single-qubit Hadamard tableau**: `H σ_a H† = hadamardPauliSign a • σ_{hadamardPauli a}`.
Conjugating a single-qubit Pauli by the Hadamard gate returns a Pauli (up to `±1`): `H X H = Z`,
`H Y H = -Y`, `H Z H = X`, `H I H = I`. A finite `Fin 4` case check reusing the existing conjugation
lemmas (`H` Hermitian, so `H† = H`). -/
theorem hadamardC_conj_pauli (a : Fin 4) :
    hadamardC * pauli a * hadamardCᴴ = hadamardPauliSign a • pauli (hadamardPauli a) := by
  have hH : hadamardCᴴ = hadamardC := hadamardC_isHermitian
  rw [hH]
  fin_cases a <;>
    simp [hadamardPauli, hadamardPauliSign, pauli, hadamardC_mul_pauliX_mul_hadamardC,
      hadamardC_mul_pauliY_mul_hadamardC, hadamardC_mul_pauliZ_mul_hadamardC, hadamardC_mul_self]

/-- **Single-qubit phase-gate tableau**: `S σ_a S† = phasePauliSign a • σ_{phasePauli a}`.
Conjugating a single-qubit Pauli by the phase gate `S = diag(1, i)` returns a Pauli (up to `±1`):
`S X S† = Y`, `S Y S† = -X`, `S Z S† = Z`, `S I S† = I` (N&C Exercise 10.39). A finite `Fin 4` case
check citing the three conjugation facts `sMatrix_conj_pauli{X,Y,Z}` and the unitarity `S S† = 1`
(the `I` case), mirroring its sibling `hadamardC_conj_pauli`. -/
theorem sMatrix_conj_pauli (a : Fin 4) :
    sMatrix * pauli a * sMatrixᴴ = phasePauliSign a • pauli (phasePauli a) := by
  have hI : sMatrix * sMatrixᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp sMatrix_mem_unitaryGroup
  fin_cases a <;>
    simp [phasePauli, phasePauliSign, pauli, sMatrix_conj_pauliX, sMatrix_conj_pauliY,
      sMatrix_conj_pauliZ, hI]

/-! ### The gate on a single wire and its conjugation action -/

/-- The single-qubit gate `G` placed on **wire `j`** of the `n`-qubit register `Fin n → Fin 2`
(identity on every other wire): `I ⊗ ⋯ ⊗ G ⊗ ⋯ ⊗ I`, i.e. the tensor product with `G` at position
`j` and `1` elsewhere. This is the one-qubit gate of a circuit acting only on qubit `j`; when `G` is
unitary so is `kronWireGate j G` (`kronWireGate_mul_conjTranspose`). -/
def kronWireGate (j : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  kronFamily (Function.update (fun _ => 1) j G)

/-- **Single-wire Clifford conjugation of a Pauli string.** For a single-qubit gate `G` with tableau
`G σ_a G† = ε a • σ_{τ a}`, conjugating the Pauli string `P_g` by `G` on wire `j` changes only wire
`j`: `kronWireGate j G · P_g · (kronWireGate j G)† = ε (g j) • P_{update g j (τ (g j))}`. This is
the sense in which a circuit built from single-wire Clifford gates acts on a Pauli string — hence on
the check matrix — one column at a time.

Proof: reducing `P_g` and the gate to `kronFamily` and applying the mixed-product property twice
(`kronFamily_mul`, `kronFamily_conjTranspose`), the `k`-th tensor factor becomes
`(update 1 j G) k · σ_{g k} · ((update 1 j G) k)†`, which is `σ_{g k}` for `k ≠ j` and
`ε (g j) • σ_{τ (g j)}` for `k = j` (the tableau `hG`). Pulling the single non-trivial scalar out
with `kronFamily_smul_family` gives the product of scalars `∏ (update 1 j (ε (g j))) = ε (g j)`
(`Finset.prod_update_of_mem`, all other factors `1`). -/
theorem kronWireGate_conj_pauliString
    {G : Matrix (Fin 2) (Fin 2) ℂ} {τ : Fin 4 → Fin 4} {ε : Fin 4 → ℂ}
    (hG : ∀ a : Fin 4, G * pauli a * Gᴴ = ε a • pauli (τ a))
    (j : Fin n) (g : Fin n → Fin 4) :
    kronWireGate j G * pauliString g * (kronWireGate j G)ᴴ
      = ε (g j) • pauliString (Function.update g j (τ (g j))) := by
  have hA : ∀ k, (Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j G) k
        * pauli (g k) * ((Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j G) k)ᴴ
      = (Function.update (fun _ => (1 : ℂ)) j (ε (g j))) k
          • pauli ((Function.update g j (τ (g j))) k) := by
    intro k
    rcases eq_or_ne k j with rfl | hk
    · simp only [Function.update_self]; exact hG (g k)
    · simp only [Function.update_of_ne hk, Matrix.conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one, one_smul]
  rw [kronWireGate, pauliString_eq_kronFamily, kronFamily_conjTranspose, kronFamily_mul,
    kronFamily_mul, congrArg kronFamily (funext hA), kronFamily_smul_family,
    Finset.prod_update_of_mem (Finset.mem_univ j), pauliString_eq_kronFamily]
  simp

/-- A single-wire gate is unitary when its single-qubit gate is:
`G G† = 1 ⟹ (kronWireGate j G)(kronWireGate j G)† = 1`. Factor-by-factor from `kronFamily_mul`
(`kronFamily_conjTranspose`): wire `j` contributes `G G† = 1`, every other wire `1 · 1† = 1`, so the
tensor product is `⨂ 1 = 1` (`kronFamily_one`). -/
theorem kronWireGate_mul_conjTranspose {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G * Gᴴ = 1)
    (j : Fin n) : kronWireGate j G * (kronWireGate j G)ᴴ = 1 := by
  have h : (fun k => (Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j G) k
        * ((Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j G) k)ᴴ)
      = fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext k
    rcases eq_or_ne k j with rfl | hk
    · simp only [Function.update_self]; exact hG
    · simp only [Function.update_of_ne hk, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [kronWireGate, kronFamily_conjTranspose, kronFamily_mul, h, kronFamily_one]


/-- **Hadamard on wire `j` conjugates a Pauli string, changing only wire `j`.** The `G = H` instance
of `kronWireGate_conj_pauliString`: `kronWireGate j H · P_g · (kronWireGate j H)† =
hadamardPauliSign (g j) • P_{update g j (hadamardPauli (g j))}`. Its check-matrix effect is the
column swap `x_j ↔ z_j`
(`pauliXBit_hadamardPauli`, `pauliZBit_hadamardPauli`). -/
theorem hadamardWire_conj_pauliString (j : Fin n) (g : Fin n → Fin 4) :
    kronWireGate j hadamardC * pauliString g * (kronWireGate j hadamardC)ᴴ
      = hadamardPauliSign (g j) • pauliString (Function.update g j (hadamardPauli (g j))) :=
  kronWireGate_conj_pauliString hadamardC_conj_pauli j g

/-- **Phase gate on wire `j` conjugates a Pauli string, changing only wire `j`.** The `G = S`
instance of `kronWireGate_conj_pauliString`: `kronWireGate j S · P_g · (kronWireGate j S)† =
phasePauliSign (g j) • P_{update g j (phasePauli (g j))}`. Its check-matrix effect is the column
operation `z_j ↦ z_j + x_j` (`pauliXBit_phasePauli`, `pauliZBit_phasePauli`). -/
theorem phaseWire_conj_pauliString (j : Fin n) (g : Fin n → Fin 4) :
    kronWireGate j sMatrix * pauliString g * (kronWireGate j sMatrix)ᴴ
      = phasePauliSign (g j) • pauliString (Function.update g j (phasePauli (g j))) :=
  kronWireGate_conj_pauliString sMatrix_conj_pauli j g

/-! ### The induced symplectic check-matrix column operations -/


/-- The `ZMod 2` check-bit form of the phase-gate tableau: `S` fixes the `X`-bit and adds it to the
`Z`-bit, `pauliBit (phasePauli a) = (x_a, z_a + x_a)`. A `4`-case check against the `ℕ`-valued laws
`pauliXBit_phasePauli` / `pauliZBit_phasePauli`. -/
theorem pauliBit_phasePauli (a : Fin 4) :
    pauliBit (phasePauli a) = ((pauliBit a).1, (pauliBit a).2 + (pauliBit a).1) := by
  fin_cases a <;> decide

end CliffordCSS

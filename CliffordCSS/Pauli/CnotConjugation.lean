import CliffordCSS.Pauli.CliffordConjugation
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Two-wire CNOT conjugation of Pauli strings and its check-matrix column operation

This file is pure mathematics : it establishes how the **two-wire
Clifford generator** — the controlled-NOT gate `CNOT` with control wire `c` and target wire `t` of
an `n`-qubit register — acts on a Pauli string (`CliffordCSS.pauliString`, `g : Fin n → Fin 4`) by
**conjugation**, and the elementary symplectic **check-matrix column operation** it induces. This is
the two-wire companion of the single-wire Hadamard/phase gates of
`CliffordCSS/Pauli/CliffordConjugation.lean`; together `{H, S, CNOT}` is the full column-operation
gate set behind the encoding circuit of Nielsen & Chuang **Problem 10.3** (the sequence of column
operations carrying the trivial check matrix `[0 | I]` of Eq. 10.124 to the standard/encoded form of
Eq. 10.125).

Conjugating a Pauli string by `CNOT` returns another Pauli string up to a `±1` phase, and on the
binary symplectic check matrix (the `(x | z)` bits `pauliXBit`, `pauliZBit` of
`CliffordCSS/Pauli/Commutation.lean`) this is exactly the column operation of Nielsen & Chuang
**Figure 10.7** (control `c`, target `t`):

* the target's `X`-bit picks up the control's: `x_t ↦ x_t + x_c` (`X_c ↦ X_c X_t`);
* the control's `Z`-bit picks up the target's: `z_c ↦ z_c + z_t` (`Z_t ↦ Z_c Z_t`);
* `x_c` and `z_t` are unchanged (`X_t ↦ X_t`, `Z_c ↦ Z_c`).

Everything names only raw matrix / index data (`Matrix`, `CliffordCSS.pauli`, `CliffordCSS.pauliString`,
`Fin n → Fin 4`, `Fin n → Fin 2`).

## The gate

Unlike the single-wire gates, `CNOT` is **entangling** and does *not* factor as a tensor product of
single-qubit gates, so the `kronFamily` factor-by-factor idiom of the `H`/`S` file does not apply
directly. Instead `CNOT` is a **permutation** of the computational basis: on the register
`Fin n → Fin 2`, `|x⟩ ↦ |x with wire t flipped by wire c⟩`, i.e. the involution
`cnotPerm c t x = update x t (x t + x c)` (mod 2). `cnotWireGate c t` is its permutation matrix.
Under `c ≠ t` it is exactly Mathlib's `Equiv.Perm.permMatrix` of the corresponding permutation
(`cnotWireGate_eq_permMatrix`), so its symmetry, self-inverse, unitarity and conjugation action are
all applications of the existing permutation-matrix API rather than hand-rolled — a genuine gate.

## What is proved

* `cnotPerm` / `cnotPerm_involutive` — the CNOT bit-permutation and that it is an involution.
* `cnotWireGate` / `cnotWireGate_eq_permMatrix` (the bridge to `Equiv.Perm.permMatrix`) /
  `cnotWireGate_conjTranspose` (symmetric) / `cnotWireGate_mul_self` (self-inverse) /
  `cnotWireGate_mul_conjTranspose`, `cnotWireGate_conjTranspose_mul` (unitarity).
* `cnotWireGate_conj_apply` — the conjugation of any matrix by the permutation reindexes both sides:
  `(P · M · Pᴴ)(i, j) = M (cnotPerm i) (cnotPerm j)`.
* `cnotCtrlPauli` / `cnotTgtPauli` / `cnotPauliSign` — the CNOT single-pair tableau: the new
  control- and target-wire Paulis and the `±1` sign in `CNOT (σ_a ⊗ σ_b) CNOT†`. Because `CNOT`
  entangles, the *new* control Pauli depends on *both* input Paulis (its `Z`-bit gains the
  target's), and likewise the new target Pauli (its `X`-bit gains the control's).
* `cnot_conj_pauliEntry` — the two-wire entry factorisation
  `σ_a(i_c,j_c) · σ_b(i_t+i_c, j_t+j_c) = ε • σ_{a'}(i_c,j_c) · σ_{b'}(i_t,j_t)` (a finite `Fin 4²`
  by `Fin 2⁴` case check), the heart of the conjugation.
* `cnotPauliString` / `cnotWireGate_conj_pauliString` — the **`n`-qubit theorem**:
  `CNOT_{c→t} · P_g · CNOT_{c→t}† = ε (g c) (g t) • P_{g'}`, where `g'` updates only wires `c`, `t`.
  Proved by the conjugation entry formula plus splitting the entrywise product off wires `t` and `c`
  (`Finset.prod_erase_mul`, `Finset.mul_prod_erase`) and the pair factorisation; the middle "rest"
  product is unchanged, and matrix entries are `ℂ` (commutative), so the two `{c,t}` factors combine
  by `cnot_conj_pauliEntry`.
* `pauliXBit_cnotTgtPauli` (`x_t ↦ x_t + x_c`), `pauliZBit_cnotTgtPauli` (`z_t` unchanged),
  `pauliXBit_cnotCtrlPauli` (`x_c` unchanged), `pauliZBit_cnotCtrlPauli` (`z_c ↦ z_c + z_t`) — the
  induced symplectic **check-matrix column operation** of Figure 10.7.

## Design notes

* The gate is defined entrywise but immediately bridged to `Equiv.Perm.permMatrix`
  (`cnotWireGate_eq_permMatrix`), so its symmetry, self-inverse, unitarity and conjugation-by-
  reindexing come from the existing Mathlib API (`Matrix.conjTranspose_permMatrix`,
  `Matrix.permMatrix_mul`/`_one`, `PEquiv.toMatrix_toPEquiv_mul`/`mul_toMatrix_toPEquiv`) rather
  than hand-rolled `Finset` sums. The `def` keeps its `c ≠ t`-free signature; the hypothesis is
  carried only in the bridge.
* The carrier is the **phase-free** `pauliString`; the `±1` acquired under conjugation is tracked as
  the explicit scalar `cnotPauliSign` (nonzero only for the pairs `X_c Z_t` and `Y_c Y_t`, where
  the two `i`-factors from `Y = iXZ` recombine to `-1`), matching the sign convention of the
  `H`/`S` file and of `pauliString_mul_comm_sign`. The check-matrix column-op lemmas are stated on
  the bits alone, discarding the sign (the check matrix is a phase-free `(x | z)` record).
* Specialising `cnotWireGate_conj_pauliString` to single-generator strings reproduces the
  Figure 10.7 / N&C Ex. 10.36 rules `CNOT X_c CNOT = X_c X_t`, `CNOT X_t CNOT = X_t`,
  `CNOT Z_c CNOT = Z_c`, `CNOT Z_t CNOT = Z_c Z_t`.
-/

open Matrix

open scoped BigOperators

namespace CliffordCSS

variable {n : ℕ}

/-! ### The CNOT bit-permutation and gate -/

/-- The **CNOT bit-permutation** with control wire `c` and target wire `t`: flip the target bit
`x t` by the control bit `x c`, `x ↦ update x t (x t + x c)` (in `Fin 2`, i.e. mod 2). This is
the action of `CNOT_{c→t}` on the computational-basis register `Fin n → Fin 2`,
`|x⟩ ↦ |x_t ⊕ x_c on wire t⟩`. It is an involution (`cnotPerm_involutive`). -/
def cnotPerm (c t : Fin n) (x : Fin n → Fin 2) : Fin n → Fin 2 :=
  Function.update x t (x t + x c)

/-- The CNOT bit-permutation is an **involution**: flipping the target by the control twice restores
the state (`(x t + x c) + x c = x t` in `Fin 2`). Requires `c ≠ t` (else the control bit is itself
altered). -/
theorem cnotPerm_involutive (c t : Fin n) (h : c ≠ t) : Function.Involutive (cnotPerm c t) := by
  intro x
  funext k
  rcases eq_or_ne k t with rfl | hk
  · simp only [cnotPerm, Function.update_self, Function.update_of_ne h]
    generalize x k = a; generalize x c = b
    fin_cases a <;> fin_cases b <;> rfl
  · simp only [cnotPerm, Function.update_of_ne hk]

/-- The **CNOT gate** `CNOT_{c→t}` (control wire `c`, target wire `t`) on the `n`-qubit register, as
the **permutation matrix** of the bit-permutation `cnotPerm c t`: `(i, j)` entry is `1` iff
`i = cnotPerm c t j`, else `0`. Under `c ≠ t` this is exactly Mathlib's `Equiv.Perm.permMatrix` of
the involution's permutation (`cnotWireGate_eq_permMatrix`), which supplies its symmetry, being its
own inverse, unitarity, and conjugation action; so it is a genuine two-qubit gate of a circuit.
The `def` is kept proof-free (no `c ≠ t` in its signature); `c ≠ t` enters only in the bridge. -/
def cnotWireGate (c t : Fin n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun i j => if i = cnotPerm c t j then (1 : ℂ) else 0

/-- **Bridge to Mathlib's permutation matrix.** For `c ≠ t`, `cnotWireGate c t` is the
`Equiv.Perm.permMatrix` of the permutation obtained from the involution `cnotPerm c t`
(`Function.Involutive.toPerm`). The entry conventions match up to `cnotPerm`'s involutivity:
`cnotWireGate i j = [i = cnotPerm j]` and `permMatrix σ i j = [σ i = j]`, and
`i = cnotPerm j ↔ cnotPerm i = j`. This reduces every gate lemma below to the existing Mathlib
permutation-matrix API. -/
theorem cnotWireGate_eq_permMatrix (c t : Fin n) (h : c ≠ t) :
    cnotWireGate c t
      = Equiv.Perm.permMatrix ℂ
          (Function.Involutive.toPerm (cnotPerm c t) (cnotPerm_involutive c t h)) := by
  have hinv := cnotPerm_involutive c t h
  ext i j
  simp only [cnotWireGate, Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Function.Involutive.coe_toPerm, Option.mem_def, Option.some.injEq]
  by_cases hij : i = cnotPerm c t j
  · rw [if_pos hij, if_pos (by rw [hij, hinv])]
  · rw [if_neg hij, if_neg (fun heq => hij (by rw [← heq, hinv]))]

/-- The inverse of the CNOT permutation equals itself (`cnotPerm` is an involution). A helper for
the gate lemmas: `permMatrix` of this permutation is symmetric and self-inverse. -/
private theorem cnotToPerm_inv (c t : Fin n) (h : c ≠ t) :
    (Function.Involutive.toPerm (cnotPerm c t) (cnotPerm_involutive c t h))⁻¹
      = Function.Involutive.toPerm (cnotPerm c t) (cnotPerm_involutive c t h) :=
  Function.Involutive.toPerm_symm (cnotPerm_involutive c t h)

/-- The CNOT gate is **symmetric** (real permutation matrix of an involution):
`(cnotWireGate c t)ᴴ = cnotWireGate c t`. Via the bridge, `Matrix.conjTranspose_permMatrix` turns
the adjoint into `permMatrix σ⁻¹`, and `σ⁻¹ = σ` (`cnotToPerm_inv`). -/
theorem cnotWireGate_conjTranspose (c t : Fin n) (h : c ≠ t) :
    (cnotWireGate c t)ᴴ = cnotWireGate c t := by
  rw [cnotWireGate_eq_permMatrix c t h, Matrix.conjTranspose_permMatrix, cnotToPerm_inv c t h]

/-- The CNOT gate is its **own inverse**: `cnotWireGate c t * cnotWireGate c t = 1`. Via the bridge,
`Matrix.permMatrix_mul` folds the product to `permMatrix (σ * σ)`, and `σ * σ = 1` (involution,
`cnotToPerm_inv`), then `Matrix.permMatrix_one`. -/
theorem cnotWireGate_mul_self (c t : Fin n) (h : c ≠ t) :
    cnotWireGate c t * cnotWireGate c t = 1 := by
  rw [cnotWireGate_eq_permMatrix c t h, ← Matrix.permMatrix_mul]
  have hone : (Function.Involutive.toPerm (cnotPerm c t) (cnotPerm_involutive c t h))
      * (Function.Involutive.toPerm (cnotPerm c t) (cnotPerm_involutive c t h)) = 1 := by
    rw [mul_eq_one_iff_eq_inv, cnotToPerm_inv c t h]
  rw [hone, Matrix.permMatrix_one]

/-- The CNOT gate is **unitary**: `cnotWireGate c t * (cnotWireGate c t)ᴴ = 1` (real symmetric
involution). -/
theorem cnotWireGate_mul_conjTranspose (c t : Fin n) (h : c ≠ t) :
    cnotWireGate c t * (cnotWireGate c t)ᴴ = 1 := by
  rw [cnotWireGate_conjTranspose c t h, cnotWireGate_mul_self c t h]


/-- **Conjugation by the CNOT permutation matrix reindexes both indices.** For any matrix `M`,
`(cnotWireGate c t · M · (cnotWireGate c t)ᴴ)(i, j) = M (cnotPerm c t i) (cnotPerm c t j)`.
Permutation-matrix conjugation is submatrix reindexing by the permutation: via the bridge and
`cnotToPerm_inv`, the two multiplications collapse to `M.submatrix σ σ.symm` by Mathlib's
`PEquiv.toMatrix_toPEquiv_mul` / `PEquiv.mul_toMatrix_toPEquiv`, and `σ = σ.symm = cnotPerm c t`. -/
theorem cnotWireGate_conj_apply (c t : Fin n) (h : c ≠ t)
    (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (i j : Fin n → Fin 2) :
    (cnotWireGate c t * M * (cnotWireGate c t)ᴴ) i j = M (cnotPerm c t i) (cnotPerm c t j) := by
  rw [cnotWireGate_eq_permMatrix c t h, Matrix.conjTranspose_permMatrix, cnotToPerm_inv c t h]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, id_eq, Function.Involutive.toPerm_symm, Function.Involutive.coe_toPerm]

/-! ### The CNOT single-pair tableau -/

/-- The **new control Pauli** in `CNOT (σ_a^c ⊗ σ_b^t) CNOT†`, as a function of the control index
`a` and target index `b` (`0 = I, 1 = X, 2 = Y, 3 = Z`). The control's `X`-bit is unchanged and its
`Z`-bit gains the target's (`z_c ↦ z_c + z_t`, since `Z_t ↦ Z_c Z_t` puts a `Z` on the control), so
it depends on both `a` and `b` (`CNOT` is entangling). -/
def cnotCtrlPauli : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 0, 3, 3], ![1, 1, 2, 2], ![2, 2, 1, 1], ![3, 3, 0, 0]]

/-- The **new target Pauli** in `CNOT (σ_a^c ⊗ σ_b^t) CNOT†`. The target's `Z`-bit is unchanged and
its `X`-bit gains the control's (`x_t ↦ x_t + x_c`, since `X_c ↦ X_c X_t` puts an `X` on the
target), so it depends on both `a` and `b`. -/
def cnotTgtPauli : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![1, 0, 3, 2], ![0, 1, 2, 3]]

/-- The **sign** `ε` in the CNOT pair tableau
`CNOT (σ_a^c ⊗ σ_b^t) CNOT† = ε • (σ_{a'}^c ⊗ σ_{b'}^t)`. It is `-1` exactly for the pairs
`(X_c, Z_t)` and `(Y_c, Y_t)`, where the two `i`-factors produced by recombining the `Y = iXZ`
factors on the two wires multiply to `-1`; otherwise `+1`. -/
def cnotPauliSign : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, 1, -1], ![1, 1, -1, 1], ![1, 1, 1, 1]]

/-- **The CNOT two-wire entry factorisation.** For the control index `a` and target index `b`, the
product of a control entry and a *shifted* target entry factorises into the transformed Paulis with
the tableau sign:
`σ_a(i_c, j_c) · σ_b(i_t+i_c, j_t+j_c) = cnotPauliSign a b • (σ_{a'}(i_c, j_c) · σ_{b'}(i_t, j_t))`
where `a' = cnotCtrlPauli a b`, `b' = cnotTgtPauli a b`. The index shift `i_t + i_c` is exactly the
CNOT bit-permutation on the target wire; this identity captures how the control couples into the
target under conjugation. A finite `Fin 4 × Fin 4` (Paulis) by `Fin 2⁴` (register bits) case check
against the explicit `pauli` entries. -/
theorem cnot_conj_pauliEntry (a b : Fin 4) (ic it jc jt : Fin 2) :
    pauli a ic jc * pauli b (it + ic) (jt + jc)
      = cnotPauliSign a b • (pauli (cnotCtrlPauli a b) ic jc * pauli (cnotTgtPauli a b) it jt) := by
  fin_cases a <;> fin_cases b <;>
    simp only [cnotCtrlPauli, cnotTgtPauli, cnotPauliSign, Matrix.cons_val',
      Matrix.cons_val_fin_one] <;>
    (fin_cases ic <;> fin_cases it <;> fin_cases jc <;> fin_cases jt <;>
      simp [pauli, pauliX, pauliY, pauliZ, Fin.add_def])

/-! ### The `n`-qubit CNOT conjugation of a Pauli string -/

/-- The **CNOT-transformed Pauli string**: `CNOT_{c→t}` conjugation changes only wire `c` (to
`cnotCtrlPauli (g c) (g t)`) and wire `t` (to `cnotTgtPauli (g c) (g t)`), leaving every other wire
fixed. The new wire-`c` and wire-`t` Paulis both depend on the *original* pair `(g c, g t)`
(`cnotWireGate_conj_pauliString`). -/
def cnotPauliString (g : Fin n → Fin 4) (c t : Fin n) : Fin n → Fin 4 :=
  Function.update (Function.update g t (cnotTgtPauli (g c) (g t))) c (cnotCtrlPauli (g c) (g t))

/-- The transformed string on the control wire:
`cnotPauliString g c t c = cnotCtrlPauli (g c) (g t)`. -/
@[simp]
theorem cnotPauliString_ctrl (g : Fin n → Fin 4) (c t : Fin n) :
    cnotPauliString g c t c = cnotCtrlPauli (g c) (g t) :=
  Function.update_self ..

/-- The transformed string on the target wire: `cnotPauliString g c t t = cnotTgtPauli (g c) (g t)`
(needs `c ≠ t`). -/
theorem cnotPauliString_tgt (g : Fin n → Fin 4) {c t : Fin n} (h : c ≠ t) :
    cnotPauliString g c t t = cnotTgtPauli (g c) (g t) := by
  simp only [cnotPauliString, Function.update_of_ne h.symm, Function.update_self]

/-- The transformed string off wires `c` and `t` is unchanged: `cnotPauliString g c t k = g k` for
`k ≠ c`, `k ≠ t`. -/
theorem cnotPauliString_of_ne (g : Fin n → Fin 4) (c t : Fin n) {k : Fin n} (hkc : k ≠ c)
    (hkt : k ≠ t) : cnotPauliString g c t k = g k := by
  simp only [cnotPauliString, Function.update_of_ne hkc, Function.update_of_ne hkt]

/-- **CNOT conjugation of a Pauli string** (control wire `c`, target wire `t`, `c ≠ t`):
`CNOT_{c→t} · P_g · CNOT_{c→t}† = cnotPauliSign (g c) (g t) • P_{cnotPauliString g c t}`.
Conjugating by `CNOT` returns a Pauli string (up to `±1`) differing from `g` only on wires `c`, `t`.

Proof: the conjugation reindexes each entry by the bit-permutation (`cnotWireGate_conj_apply`),
`P_g(cnotPerm i, cnotPerm j) = ∏ₖ σ_{gₖ}((cnotPerm i)ₖ)((cnotPerm j)ₖ)`. Splitting the entrywise
product off wire `t` and then wire `c` (`Finset.prod_erase_mul`, `Finset.mul_prod_erase`; `c ≠ t`),
only the target factor carries the coupled shift `(i_t + i_c, j_t + j_c)`; the "rest" product over
the other wires is literally unchanged (`cnotPauliString_of_ne`), and — matrix entries being `ℂ`,
commutative — the `{c, t}` factors recombine by the pair factorisation `cnot_conj_pauliEntry`. -/
theorem cnotWireGate_conj_pauliString (c t : Fin n) (h : c ≠ t) (g : Fin n → Fin 4) :
    cnotWireGate c t * pauliString g * (cnotWireGate c t)ᴴ
      = cnotPauliSign (g c) (g t) • pauliString (cnotPauliString g c t) := by
  ext i j
  rw [cnotWireGate_conj_apply c t h, Matrix.smul_apply, pauliString_apply, pauliString_apply,
    smul_eq_mul]
  have hc_mem : c ∈ Finset.univ.erase t := Finset.mem_erase.mpr ⟨h, Finset.mem_univ c⟩
  have hrest : ∀ k ∈ (Finset.univ.erase t).erase c,
      pauli (g k) ((cnotPerm c t i) k) ((cnotPerm c t j) k)
        = pauli (cnotPauliString g c t k) (i k) (j k) := by
    intro k hk
    have hkt : k ≠ t := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkc : k ≠ c := Finset.ne_of_mem_erase hk
    simp only [cnotPerm, Function.update_of_ne hkt, cnotPauliString_of_ne g c t hkc hkt]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ t), ← Finset.mul_prod_erase _ _ hc_mem]
  rw [← Finset.prod_erase_mul (a := t)
        (f := fun k => pauli (cnotPauliString g c t k) (i k) (j k)) _ (Finset.mem_univ t),
      ← Finset.mul_prod_erase _
        (f := fun k => pauli (cnotPauliString g c t k) (i k) (j k)) hc_mem]
  rw [Finset.prod_congr rfl hrest, cnotPauliString_ctrl, cnotPauliString_tgt g h]
  simp only [cnotPerm, Function.update_self, Function.update_of_ne h]
  have key := cnot_conj_pauliEntry (g c) (g t) (i c) (i t) (j c) (j t)
  rw [smul_eq_mul] at key
  set R := ∏ x ∈ (Finset.univ.erase t).erase c,
    pauli (cnotPauliString g c t x) (i x) (j x) with hR
  linear_combination R * key

/-! ### The induced symplectic check-matrix column operation (Figure 10.7) -/


end CliffordCSS

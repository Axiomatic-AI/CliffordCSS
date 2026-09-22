import CliffordCSS.Symplectic.CheckMatrixSymplectic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Concatenating two `[n, 1]` stabilizer codes (Nielsen & Chuang, Exercise 10.62)

This file is pure mathematics : it sets up the **explicit generator
construction** for the concatenation of two stabilizer codes and the reusable `𝔽₂` symplectic
linear-algebra toolkit its proofs consume. Everything here names only raw matrix / index data
(`Matrix`, `CliffordCSS.pauliString`, `CliffordCSS.checkRow`, `Fin n → Fin 4`, `ZMod 2`).

> **Exercise 10.62.** Show by explicit construction of generators for the stabilizer that
> concatenating an `[n₁, 1]` stabilizer code with an `[n₂, 1]` stabilizer code gives an `[n₁n₂, 1]`
> stabilizer code. — Nielsen & Chuang (p. 482).

## The construction

An `[n, 1]` stabilizer code (with distinguished logical operators) is packaged as `StabCode1 g`:
`g = n − 1` phase-free Pauli-string generators on `n = g + 1` qubits, together with a logical
`X̄`/`Z̄` pair. Its fields are N&C's defining data — the generators are **independent** (their check
rows are `𝔽₂`-linearly independent, Prop 10.3) and **commuting**, and `X̄, Z̄` form a **hyperbolic
pair** in the normalizer (each commutes with every generator; they anticommute with each other) —
exactly what makes `⟨gen⟩` an `[n, 1]` code (`n − 1` independent commuting generators ⇒ `k = 1`)
with logical operators `X̄, Z̄`.

**Concatenation.** Take `C₁ : StabCode1 g₁` as the *inner* code (`n₁ = g₁ + 1` qubits per block) and
`C₂ : StabCode1 g₂` as the *outer* code (`n₂ = g₂ + 1` blocks). The concatenated register has
`n₂ · n₁ = (g₂+1)(g₁+1)` qubits, indexed by `Fin (g₂+1) × Fin (g₁+1)` (block, inner qubit),
identified with `Fin ((g₂+1)(g₁+1))` via `finProdFinEquiv`. The generators (`concatRaw`,
`concatGen`), indexed by `(Fin (g₂+1) × Fin g₁) ⊕ Fin g₂`, are:

* the **inner** generators — `C₁.gen a` on block `b`, identity on the other blocks (`inl (b, a)`),
  `n₂ · g₁` of them; and
* the **encoded outer** generators — the outer generator `C₂.gen j`, with each single-qubit Pauli on
  block `b` replaced (via `encStr`) by the inner logical operator `X̄^{x} Z̄^{z}` realizing it
  (`inr j`), `g₂` of them.

This is `n₂ · g₁ + g₂ = (g₂+1)(g₁+1) − 1 = n₁n₂ − 1` generators on `n₁n₂` qubits (`concatIdx_card`):
`n₁n₂ − 1` independent commuting generators ⇒ `k = 1`, an `[n₁n₂, 1]` code. The independence and
commutation proofs, and the dimension conclusion via Proposition 10.5, are in the sibling files.

## The symplectic toolkit

The independence and commutation arguments are `𝔽₂` symplectic linear algebra over the check rows.
This file provides the general-index check rows (`checkVecG`, `checkRowG`) and the reusable facts
about `CliffordCSS.symplecticForm`: it is bi-additive (`symplecticForm_add_left`), `𝔽₂`-linear
(`symplecticForm_smul_left`), **alternating** (`symplecticForm_self`, `= 0` over `ZMod 2`) and
**symmetric** (`symplecticForm_comm`), invariant under a qubit relabeling
(`symplecticForm_comp_sumMap`), and the key **hyperbolic-pair independence** lemma
`linearIndependent_sumElim_hyperbolic`: a linearly independent family orthogonal to a hyperbolic
pair `(x, z)` (`symplecticForm x z = 1`) extends, by that pair, to a linearly independent family.
-/

open Matrix

open scoped BigOperators

namespace CliffordCSS

/-! ### General-index check-matrix rows -/

variable {ι κ : Type*}

/-- The **check-matrix row** `r(g) = (x_g | z_g)` of a Pauli string over an *arbitrary* qubit index
`ι` — the `X`-part and `Z`-part over `ZMod 2` (`CliffordCSS.checkRow` for `ι = Fin n`, but with the
index kept general so it can name a product index `Fin (g₂+1) × Fin (g₁+1)`). -/
def checkRowG (g : ι → Fin 4) : (ι → ZMod 2) × (ι → ZMod 2) :=
  (fun k => (pauliBit (g k)).1, fun k => (pauliBit (g k)).2)

/-- The flat `2|ι|`-vector check row `r(g)` over an arbitrary qubit index `ι`, the `X`-bit on
`Sum.inl` and the `Z`-bit on `Sum.inr` (`CliffordCSS.checkVec` for `ι = Fin n`). -/
def checkVecG (g : ι → Fin 4) : ι ⊕ ι → ZMod 2 :=
  Sum.elim (checkRowG g).1 (checkRowG g).2


/-- On the `Fin n` qubit index the general flat check row is the standard `checkVec`. -/
@[simp] theorem checkVecG_eq {n : ℕ} (g : Fin n → Fin 4) : checkVecG g = checkVec g := rfl

/-- **The check row of the identity string is zero**: `r(𝟙) = 0`, since every single-qubit Pauli is
`I` (`pauliBit 0 = (0, 0)`). This is the check-vector reading of "the identity generator contributes
nothing" — used both by `encStr_checkVec` (the `I ↦ 𝟙` case) and when an inner concatenated
generator misses a block. -/
@[simp] theorem checkVec_const_zero {n : ℕ} : checkVec (fun _ : Fin n => (0 : Fin 4)) = 0 := by
  ext s; cases s <;> simp [checkVec, checkRow, pauliBit, pauliXBit, pauliZBit]

/-! ### The `symplecticForm` toolkit -/

variable [Fintype ι] [DecidableEq ι]


/-- **`symplecticForm` is symmetric** (over `ZMod 2`, where `Λ` is symmetric): `ω(x, y) = ω(y, x)`. -/
theorem symplecticForm_comm (x y : ι ⊕ ι → ZMod 2) :
    symplecticForm x y = symplecticForm y x := by
  rw [symplecticForm_apply, symplecticForm_apply,
    dotProduct_comm (x ∘ Sum.inl) (y ∘ Sum.inr), dotProduct_comm (x ∘ Sum.inr) (y ∘ Sum.inl)]
  ring


/-! ### The hyperbolic-pair independence lemma -/


/-! ### An `[n, 1]` stabilizer code with distinguished logical operators -/

/-- An **`[n, 1]` stabilizer code with a chosen logical `X̄`/`Z̄` pair**, on `n = g + 1` qubits with
`g` generators — the data N&C's construction consumes. `gen` are `g` phase-free Pauli-string
generators; they **commute** (`gen_commute`) and are **independent** (`gen_indep`: their check rows
are `𝔽₂`-linearly independent, N&C Prop 10.3), so `⟨gen⟩` is an `[g+1, 1]` stabilizer (`k = 1`). The
logical operators `logX`, `logZ` lie in the normalizer — each **commutes** with every generator
(`logX_commute`, `logZ_commute`) — and form a **hyperbolic pair**: they **anticommute**
(`logXZ_anticommute`). -/
structure StabCode1 (g : ℕ) where
  /-- The `g = n − 1` phase-free stabilizer generators on `n = g + 1` qubits. -/
  gen : Fin g → (Fin (g + 1) → Fin 4)
  /-- The logical `X̄` operator. -/
  logX : Fin (g + 1) → Fin 4
  /-- The logical `Z̄` operator. -/
  logZ : Fin (g + 1) → Fin 4
  /-- The generators pairwise commute. -/
  gen_commute : ∀ i j, Commute (pauliString (gen i)) (pauliString (gen j))
  /-- The generators are independent: their check rows are `𝔽₂`-linearly independent (Prop 10.3). -/
  gen_indep : LinearIndependent (ZMod 2) (fun i => checkRow (gen i))
  /-- `X̄` commutes with every generator (it is in the normalizer). -/
  logX_commute : ∀ i, Commute (pauliString logX) (pauliString (gen i))
  /-- `Z̄` commutes with every generator (it is in the normalizer). -/
  logZ_commute : ∀ i, Commute (pauliString logZ) (pauliString (gen i))
  /-- `X̄` and `Z̄` anticommute (they form a hyperbolic logical pair). -/
  logXZ_anticommute : ¬ Commute (pauliString logX) (pauliString logZ)

variable {g₁ g₂ : ℕ}


/-! ### The concatenated generators commute (Exercise 10.62, commutation half)

The `n₁n₂ − 1` concatenated generators pairwise **commute**. Via Exercise 10.33
(`pauliString_commute_iff_symplecticForm`) this reduces to the vanishing of the twisted product
`ω` of their check rows, which — by the *block decomposition* of `ω` over the `Fin (g₂+1)` blocks —
splits into three cases, each closed by an inner-code symplectic relation:

* **inner–inner** (`inl (b, a)` vs `inl (b', a')`): the two operators are supported on single
  blocks; disjoint blocks contribute `0`, a shared block contributes `ω(r(gᵃ), r(gᵃ'))` which is
  `0` because the *inner* generators commute;
* **inner–encoded-outer** (`inl (b, a)` vs `inr j`): only block `b` contributes, and there the
  encoded outer Pauli is an `𝔽₂`-combination of `X̄, Z̄`, each commuting with every inner generator;
* **encoded-outer–encoded-outer** (`inr j` vs `inr j'`): each block's contribution is the
  single-qubit symplectic pairing of the *outer* Paulis (the `X̄, Z̄` hyperbolic relation
  `ω(r(X̄), r(Z̄)) = 1` cancelling the encoding), so the block sum reassembles the *outer* twisted
  product `ω(r(gⱼ), r(gⱼ'))`, which is `0` because the outer generators commute.
-/


end CliffordCSS

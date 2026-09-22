import CliffordCSS.Pauli.BasisChange

/-!
# Commutation of Pauli strings and the symplectic form (Nielsen & Chuang, Ex. 10.33)

This file is pure mathematics : it proves that any two `n`-fold
Pauli strings (`CliffordCSS.pauliString`, indexed by `g : Fin n → Fin 4`) either **commute** or
**anticommute**, with the dichotomy governed entirely by the **binary symplectic form** of their
check-matrix rows. This is the algebraic heart of the stabilizer formalism — Nielsen & Chuang,
Exercise 10.33: two elements of the Pauli group commute iff `r(g) Λ r(g')ᵀ = 0 (mod 2)`, where
`r(·)` is the `(x | z)` check-matrix row and `Λ = [[0, I], [I, 0]]` is the symplectic form. Because
commutation is unchanged by the overall phase, the phase-free `pauliString` (which carries no `±1,
±i` prefactor) is the correct carrier for this fact.

Everything here names only raw matrix / index data (`Matrix`, `CliffordCSS.pauli`, `CliffordCSS.
pauliString`, `Fin n → Fin 4`). It is shared infrastructure for the Chapter 10
stabilizer-code program (Propositions 10.3–10.5, Theorems 10.6–10.8, and the encoding circuit of
Problem 10.3), each of which needs to know when Pauli-group generators commute.

## The binary symplectic representation

Each single-qubit Pauli index `a : Fin 4` (`0 = I, 1 = X, 2 = Y, 3 = Z`) has an **X-bit** and a
**Z-bit** (`pauliXBit`, `pauliZBit`): `I ↦ (0,0)`, `X ↦ (1,0)`, `Y ↦ (1,1)`, `Z ↦ (0,1)`. A Pauli
string `g : Fin n → Fin 4` thus has check-matrix row `r(g) = (x_g | z_g)` with `x_g k = pauliXBit
(g k)`, `z_g k = pauliZBit (g k)`. The **symplectic pairing** of `a, b` is `singlePauliAnticomm a b
= x_a z_b + z_a x_b`, and the total pairing of two strings is `pauliAnticommCount g h = Σ_k
(x_{g,k} z_{h,k} + z_{g,k} x_{h,k})` — exactly `r(g) Λ r(g')ᵀ`. Its **parity** (`Even`) is the
mod-2 symplectic condition of Exercise 10.33.

## What is proved

* `pauli_mul_comm_sign` — the single-qubit sign law `σ_a σ_b = (-1)^{singlePauliAnticomm a b} σ_b
  σ_a`: two single-qubit Paulis commute or anticommute, and the symplectic pairing says which.
* `pauliString_mul_self` — each Pauli string is an **involution**, `P_g P_g = I` (so `P_g` is
  unitary / its own inverse).
* `pauliString_mul_comm_sign` — the `n`-qubit sign law `P_g P_h = (-1)^{pauliAnticommCount g h} P_h
  P_g`, obtained factor-by-factor from the single-qubit law via the tensor mixed-product property
  (`kronFamily_mul`) and the scalar pull-out `kronFamily_smul_family`.
* `pauliAnticommCount_symm` — the symplectic form is symmetric, `pauliAnticommCount g h =
  pauliAnticommCount h g` (so commutation is a symmetric relation).
* `pauliString_commute_iff` — **Nielsen & Chuang, Exercise 10.33**: `Commute P_g P_h ↔ Even
  (pauliAnticommCount g h)`. The `⇐` direction reads the sign as `+1`; the `⇒` direction uses that
  an odd pairing forces `P_g P_h = -P_g P_h`, hence `P_g P_h = 0`, contradicting `(P_g P_h)(P_h P_g)
  = I` (the involution `pauliString_mul_self`).

## Design notes

* The pairing `singlePauliAnticomm` / `pauliAnticommCount` is a **natural-number count** (it equals
  `2` on the diagonal `Y, Y` pair, not `1`), and it is only its **parity** that is the symplectic
  invariant — `(-1)^{count}` and `Even count` are parity-invariant, so this faithfully realizes the
  `(mod 2)` symplectic form while keeping a clean `ℕ` exponent for the sign.
* The proofs reduce everything to the per-qubit tensor-factorisation lemmas `kronFamily_mul` /
  `kronFamily_one` of `CliffordCSS/Pauli/BasisChange.lean`; the single-qubit base case
  `pauli_mul_comm_sign` is a finite `4 × 4` case check.
-/

open Matrix

open scoped BigOperators

namespace CliffordCSS

/-! ### Single-qubit symplectic data -/

/-- The **X-bit** of a single-qubit Pauli index: `I, X, Y, Z ↦ 0, 1, 1, 0`. It is `1` exactly for
the Paulis (`X`, `Y`) that contain an `X` factor, i.e. the X-part of the binary symplectic
representation of a single-qubit Pauli. -/
def pauliXBit : Fin 4 → ℕ := ![0, 1, 1, 0]

/-- The **Z-bit** of a single-qubit Pauli index: `I, X, Y, Z ↦ 0, 0, 1, 1`. It is `1` exactly for
the Paulis (`Y`, `Z`) that contain a `Z` factor, i.e. the Z-part of the binary symplectic
representation of a single-qubit Pauli. -/
def pauliZBit : Fin 4 → ℕ := ![0, 0, 1, 1]

/-- The **single-qubit symplectic pairing** of two Pauli indices, `x_a z_b + z_a x_b`. It is the
per-qubit contribution to the symplectic form `r(g) Λ r(g')ᵀ`, and its parity is the single-qubit
commutation indicator: `0 (mod 2)` when `σ_a`, `σ_b` commute, `1` when they anticommute. -/
def singlePauliAnticomm (a b : Fin 4) : ℕ :=
  pauliXBit a * pauliZBit b + pauliZBit a * pauliXBit b

/-- **Single-qubit commutation/anticommutation sign law**: `σ_a σ_b = (-1)^{singlePauliAnticomm a
b} · σ_b σ_a`. Any two single-qubit Paulis either commute (sign `+1`, symplectic pairing even) or
anticommute (sign `-1`, pairing odd); the symplectic pairing `singlePauliAnticomm` decides which.
Proved by the finite `4 × 4` case check on `a, b`. -/
theorem pauli_mul_comm_sign (a b : Fin 4) :
    pauli a * pauli b = (-1 : ℂ) ^ singlePauliAnticomm a b • (pauli b * pauli a) := by
  fin_cases a <;> fin_cases b <;>
    simp only [singlePauliAnticomm, pauliXBit, pauliZBit] <;>
    norm_num [pauli] <;>
    (ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ])

/-! ### Commutation of `n`-qubit Pauli strings -/

variable {n : ℕ}

/-- The **symplectic form** (total anticommutation pairing) of two Pauli strings, `Σ_k
singlePauliAnticomm (g k) (h k)`. This is `r(g) Λ r(g')ᵀ` for the check-matrix rows `r(g) = (x_g |
z_g)` and symplectic form `Λ = [[0, I], [I, 0]]`; its parity is the mod-2 quantity of Nielsen &
Chuang, Exercise 10.33. -/
def pauliAnticommCount (g h : Fin n → Fin 4) : ℕ := ∑ k, singlePauliAnticomm (g k) (h k)


/-- Each Pauli string is an **involution**: `P_g P_g = I`. Factor-by-factor `σ_{gₖ}² = I`
(`pauli_mul_self`), so the tensor product is `⨂ₖ I = I` (`kronFamily_one`). In particular `P_g` is
its own inverse, hence unitary. -/
theorem pauliString_mul_self (g : Fin n → Fin 4) : pauliString g * pauliString g = 1 := by
  rw [pauliString_eq_kronFamily, kronFamily_mul]
  simp only [pauli_mul_self]
  exact kronFamily_one

/-- **The `n`-qubit commutation/anticommutation sign law**: `P_g P_h = (-1)^{pauliAnticommCount g h}
· P_h P_g`. The Pauli strings commute or anticommute as a whole, and the total symplectic pairing
decides which. Obtained factor-by-factor from the single-qubit law (`pauli_mul_comm_sign`) via the
tensor mixed-product property (`kronFamily_mul`): each qubit contributes its sign `(-1)^{…}`, and
the product of signs is `(-1)` to the sum of the pairings (`Finset.prod_pow_eq_pow_sum`). -/
theorem pauliString_mul_comm_sign (g h : Fin n → Fin 4) :
    pauliString g * pauliString h =
      (-1 : ℂ) ^ pauliAnticommCount g h • (pauliString h * pauliString g) := by
  rw [pauliString_eq_kronFamily g, pauliString_eq_kronFamily h, kronFamily_mul]
  have hfac : (fun k => pauli (g k) * pauli (h k))
      = (fun k => (-1 : ℂ) ^ singlePauliAnticomm (g k) (h k) • (pauli (h k) * pauli (g k))) := by
    funext k; exact pauli_mul_comm_sign (g k) (h k)
  rw [hfac, kronFamily_smul_family, Finset.prod_pow_eq_pow_sum, ← kronFamily_mul,
    ← pauliString_eq_kronFamily, ← pauliString_eq_kronFamily]
  rfl

/-- **Nielsen & Chuang, Exercise 10.33** (the symplectic check-matrix commutation condition): two
Pauli strings commute iff their symplectic form vanishes mod 2,
`Commute P_g P_h ↔ Even (pauliAnticommCount g h)`. The `⇐` direction reads the sign law
(`pauliString_mul_comm_sign`) with sign `+1`. For `⇒`, an odd pairing would give sign `-1`, so
`P_g P_h = -(P_h P_g) = -(P_g P_h)` (using commutation), forcing `P_g P_h = 0`; but the involution
property (`pauliString_mul_self`) gives `(P_g P_h)(P_h P_g) = I`, contradicting `0 = I`. -/
theorem pauliString_commute_iff (g h : Fin n → Fin 4) :
    Commute (pauliString g) (pauliString h) ↔ Even (pauliAnticommCount g h) := by
  have hinv : (pauliString g * pauliString h) * (pauliString h * pauliString g) = 1 := by
    rw [mul_assoc, ← mul_assoc (pauliString h), pauliString_mul_self, one_mul,
      pauliString_mul_self]
  constructor
  · intro hcomm
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsign : (-1 : ℂ) ^ pauliAnticommCount g h = -1 := hodd.neg_one_pow
    have key := pauliString_mul_comm_sign g h
    rw [hsign, neg_one_smul, hcomm.eq] at key
    have hz : pauliString h * pauliString g = 0 := by
      have h2 : (2 : ℂ) • (pauliString h * pauliString g) = 0 := by
        rw [two_smul]; nth_rewrite 2 [key]; rw [add_neg_cancel]
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    rw [hcomm.eq, hz, zero_mul] at hinv
    exact zero_ne_one hinv
  · intro heven
    have hsign : (-1 : ℂ) ^ pauliAnticommCount g h = 1 := heven.neg_one_pow
    have key := pauliString_mul_comm_sign g h
    rw [hsign, one_smul] at key
    exact key


end CliffordCSS

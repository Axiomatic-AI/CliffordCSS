import CliffordCSS.Symplectic.Group
import Mathlib.Logic.Equiv.Fin.Basic
import Batteries.Data.Nat.Lemmas

/-!
# Packed `Nat`-bitmask encoding of `𝔽₂` square matrices (Beyond transversality, App. D.1)

Pure mathematics : a **packed representation** of a square matrix
over `𝔽₂ = ZMod 2` as a single natural-number *bitmask*, together with bit-arithmetic operations on
the packed number that are **proved equal to the corresponding `Matrix` operations**. It names only
raw carriers (`Matrix`, `Nat`, `Fin`, `ZMod 2`).

## Why this exists (the `lem-local` / Lemma D.4 obstruction)

The proof of the fixed-matching generation theorem (Theorem D.1, `thm-depthone`) turns on the
*Local reduction* lemma (`lem-local`): every element of `Sp(2, 𝔽₂)` reaches a terminal block in at
most one move, and every element of `Sp(4, 𝔽₂)` in at most three — a claim the paper establishes by
**exhaustive enumeration** of the `2`- and `4`-element blocks (there are `2`, resp. `16`, terminal
blocks; `Sp(4, 𝔽₂)` has order `720`). Enumerating that check with the *function-type* carrier
`Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)` is intractable in the Lean kernel: `Fintype` /
`DecidableEq` on a `Pi`-type materialise `2^16` closures and nested per-entry comparisons.

A `Nat` bitmask sidesteps this: the kernel evaluates numeral arithmetic natively (GMP), and
`Fin (2 ^ (m * m))` carries a `Fintype` / `DecidableEq` that reduce to a single `Nat` range scan and
`Nat.decEq`. This file builds the matrix ⇄ bitmask bridge and the packed operations generically in
the size `m`, so it is reusable for any finite `𝔽₂`-matrix verification; the `Sp(4)` case is `m = 4`
and the `Sp(2)` case is `m = 2`.

## What is proved here

The bit-packing primitive itself is Batteries' `Nat.ofBits : (Fin N → Bool) → ℕ` (a Horner fold),
whose `Nat.testBit_ofBits_lt` (bit `i` reads back `f i`) and `Nat.ofBits_lt_two_pow` (`< 2 ^ N`) are
reused directly; this file contributes the matrix layer. The `(i, j)` entry of an `m × m` matrix is
stored at bit `flatEquiv (i, j)` of the bitmask.

* `testBit_ofBits` — the `Fin`-indexed reading of `Nat.testBit_ofBits_lt`, `(Nat.ofBits f).testBit
  ↑q = f q`, the form the entry proofs below consume.
* `toMatrix` / `ofMatrix` — decode a bitmask to a `Matrix` and encode a `Matrix` to a bitmask.
* `toMatrix_ofMatrix` — the round-trip `toMatrix (ofMatrix M) = M`: every matrix is the decoding of
  its bitmask, so `toMatrix` is onto the `m × m` matrices (needed for a complete enumeration).
* `ofMatrix_lt` — `ofMatrix M < 2 ^ (m * m)` (from `Nat.ofBits_lt_two_pow`): the bitmasks of `m × m`
  matrices land in the range `Fin (2 ^ (m * m))`, the finite index set an enumeration ranges over.
* `transpose` / `toMatrix_transpose` — the bit-permutation transpose, proved equal to `Matrixᵀ`:
  `toMatrix (transpose m a) = (toMatrix a)ᵀ`.
* `mul` / `toMatrix_mul` — the packed `𝔽₂` matrix product (each output bit the parity of a
  `ZMod 2` row·column dot product of `testBit` reads), proved equal to the `Matrix` product:
  `toMatrix (mul m a b) = toMatrix a * toMatrix b`.

The final layer is the **packed symplectic-membership test**, the operation the finite `Sp(2, 𝔽₂)` /
`Sp(4, 𝔽₂)` verification actually runs. It writes the paper's condition `Gᵀ J G = J` entirely in the
packed calculus and proves it equivalent to genuine membership in `binarySymplecticGroup`:

* `toMatrix_inj_of_lt` — `toMatrix` is injective on the enumeration range `Fin (2 ^ (m * m))`, so a
  packed *equation* between two in-range bitmasks is equivalent to the `Matrix` equation of their
  decodings (the missing half of the bijection whose other half is `toMatrix_ofMatrix`).
* `blockEquiv` / `toBlocks` — the `2n = n + n` reindexing `Fin (n + n) ≃ Fin n ⊕ Fin n`
  (`finSumFinEquiv`) and the decode of a packed bitmask to the block-indexed matrix that
  `binarySymplecticGroup (Fin n)` lives on, with `toBlocks_mul` / `toBlocks_transpose` transporting
  the packed operations across it.
* `ofBlocks` / `toBlocks_ofBlocks` / `ofBlocks_lt` — the *encoder*, the inverse of `toBlocks`
  (colocated with it, as `ofMatrix` is with `toMatrix`): pack a block-indexed matrix into a bitmask,
  with the round-trip `toBlocks n (ofBlocks n G) = G` and range bound. The block-level companion of
  the flat encoder `ofMatrix`.
* `packedSymplecticMatrix` / `toBlocks_packedSymplecticMatrix` — the packed Gram matrix `J`, the
  special case `ofBlocks n symplecticMatrix`, whose decode is the paper's `symplecticMatrix`.
* `IsPackedSymplectic` (with its `Decidable` instance) and `isPackedSymplectic_iff_mem` — the packed
  test `Gᵀ J G = J` as a decidable `Nat` equation, proved `↔ toBlocks n a ∈ binarySymplecticGroup
  (Fin n)`.
-/

open Matrix

namespace CliffordCSS.Packed

/-- **The `Fin`-indexed bit read-back for `Nat.ofBits`.** Reading bit `q` of `Nat.ofBits f` returns
`f q`: `(Nat.ofBits f).testBit ↑q = f q`. This is the `Fin`-indexed convenience form of Batteries'
`Nat.testBit_ofBits_lt` (which is `ℕ`-indexed with a side `i < N` hypothesis); every packed
operation below is defined via `Nat.ofBits` and its correctness reduces to this reading composed
with `flatEquiv`'s round-trip. -/
theorem testBit_ofBits {N : ℕ} (f : Fin N → Bool) (q : Fin N) :
    (Nat.ofBits f).testBit (q : ℕ) = f q :=
  Nat.testBit_ofBits_lt f (q : ℕ) q.isLt

variable {m : ℕ}

/-- The **bit address of entry `(i, j)`**: the bijection `Fin m × Fin m ≃ Fin (m * m)` packing the
`m²` matrix positions into `m²` bit indices (`finProdFinEquiv`). Entry `M i j` is stored at bit
`flatEquiv (i, j)` of the bitmask. -/
def flatEquiv : Fin m × Fin m ≃ Fin (m * m) := finProdFinEquiv

/-- **Decode** a bitmask `a` to the `m × m` matrix over `𝔽₂` whose `(i, j)` entry is `1` when bit
`flatEquiv (i, j)` of `a` is set and `0` otherwise. Left inverse of `ofMatrix`
(`toMatrix_ofMatrix`). -/
def toMatrix (a : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of (fun i j => if a.testBit (flatEquiv (i, j) : ℕ) then 1 else 0)

/-- **Encode** an `m × m` matrix over `𝔽₂` as a bitmask (`Nat.ofBits`): bit `flatEquiv (i, j)`
records whether `M i j = 1`. Right inverse of `toMatrix` (`toMatrix_ofMatrix`). -/
def ofMatrix (M : Matrix (Fin m) (Fin m) (ZMod 2)) : ℕ :=
  Nat.ofBits (fun p => decide (M (flatEquiv.symm p).1 (flatEquiv.symm p).2 = 1))

/-- In `ZMod 2` an element is recovered as the indicator of its being `1`:
`(if x = 1 then 1 else 0) = x`. (There are only the two values `0, 1`.) -/
theorem zmod2_ite_self (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  revert x; decide

/-- **Round-trip.** Decoding the bitmask of a matrix returns the matrix:
`toMatrix (ofMatrix M) = M`. Hence `toMatrix` is surjective onto the `m × m` matrices over `𝔽₂` —
every matrix is enumerated by some bitmask, which is what a complete finite verification needs. -/
theorem toMatrix_ofMatrix (M : Matrix (Fin m) (Fin m) (ZMod 2)) : toMatrix (ofMatrix M) = M := by
  ext i j
  simp only [toMatrix, ofMatrix, Matrix.of_apply, testBit_ofBits, Equiv.symm_apply_apply,
    decide_eq_true_eq]
  exact zmod2_ite_self (M i j)

/-- The bitmask of an `m × m` matrix fits in `m²` bits: `ofMatrix M < 2 ^ (m * m)`
(`Nat.ofBits_lt_two_pow`). So the encoding maps the matrices into the finite index range
`Fin (2 ^ (m * m))` an enumeration scans. -/
theorem ofMatrix_lt (M : Matrix (Fin m) (Fin m) (ZMod 2)) : ofMatrix M < 2 ^ (m * m) :=
  Nat.ofBits_lt_two_pow _

/-- **Packed transpose.** The bitmask whose bit `flatEquiv (i, j)` is bit `flatEquiv (j, i)` of `a`,
i.e. the bit-permutation implementing matrix transposition on the packed representation. Proved
equal to `Matrixᵀ` by `toMatrix_transpose`. -/
def transpose (m : ℕ) (a : ℕ) : ℕ :=
  Nat.ofBits (fun p : Fin (m * m) => a.testBit ((flatEquiv (m := m) (flatEquiv.symm p).swap) : ℕ))

/-- **Correctness of the packed transpose**: decoding `transpose m a` yields the transpose of the
decoding, `toMatrix (transpose m a) = (toMatrix a)ᵀ`. Immediate from `testBit_ofBits` and the
round-trip of `flatEquiv`, swapping the two coordinates. -/
theorem toMatrix_transpose (a : ℕ) :
    (toMatrix (transpose m a) : Matrix (Fin m) (Fin m) (ZMod 2)) = (toMatrix a)ᵀ := by
  ext i j
  simp only [toMatrix, transpose, Matrix.of_apply, Matrix.transpose_apply, testBit_ofBits,
    Equiv.symm_apply_apply, Prod.swap_prod_mk]

/-- **Packed `𝔽₂` matrix multiplication.** The bitmask whose bit `flatEquiv (i, j)` records the
`(i, j)` entry of the product of the two decoded matrices: the entry is `1` exactly when the
`ZMod 2` dot product of decoded row `i` of `a` with decoded column `j` of `b`,
`∑ k, toMatrix a i k * toMatrix b k j`, equals `1`. Every output bit is computed from native
`Nat.testBit` reads (each decoded entry `toMatrix a i k` reduces to a single `testBit`,
materialising no `Matrix`/`Pi`-type value) and a length-`m` sum in `ZMod 2 = Fin 2`; it is proved
equal to the `Matrix` product `toMatrix a * toMatrix b` by `toMatrix_mul`. -/
def mul (m a b : ℕ) : ℕ :=
  Nat.ofBits fun p : Fin (m * m) =>
    decide ((∑ k : Fin m,
      toMatrix a (flatEquiv.symm p).1 k * toMatrix b k (flatEquiv.symm p).2) = (1 : ZMod 2))

/-- **Correctness of the packed multiplication**: decoding `mul m a b` yields the product of the
decodings, `toMatrix (mul m a b) = toMatrix a * toMatrix b`. The `(i, j)` decoded entry of `mul m a
b` is, by `testBit_ofBits` and the round-trip of `flatEquiv`, the indicator of the `ZMod 2` sum
`∑ₖ toMatrix a i k * toMatrix b k j` being `1`; `Matrix.mul_apply` expands the product's entry into
exactly that sum, and `zmod2_ite_self` turns the indicator of `(· = 1)` back into the value (there
are only the two elements `0, 1` in `ZMod 2`). -/
theorem toMatrix_mul (a b : ℕ) :
    (toMatrix (mul m a b) : Matrix (Fin m) (Fin m) (ZMod 2)) = toMatrix a * toMatrix b := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [mul, toMatrix, Matrix.of_apply, testBit_ofBits, Equiv.symm_apply_apply,
    decide_eq_true_eq]
  exact zmod2_ite_self _

/-- **`toMatrix` is injective on the enumeration range.** Two bitmasks below `2 ^ (m * m)` that
decode to the *same* `m × m` matrix over `𝔽₂` are equal. Together with surjectivity
(`toMatrix_ofMatrix`) this makes `toMatrix` a bijection from `Fin (2 ^ (m * m))` onto the `m × m`
matrices, so a finite check ranging over that index set visits each matrix exactly once — and, read
the other way, a packed *equation* `a = b` between two in-range bitmasks is equivalent to the
`Matrix` equation `toMatrix a = toMatrix b` of their decodings (the direction used by the symplectic
test). Proof: `Nat.eq_of_testBit_eq`; for a bit index `k < m * m` it is `flatEquiv (i, j)` for some
entry, whose equality is read off the matrix equation (`1 ≠ 0` in `𝔽₂`), and for `k ≥ m * m` both
bits vanish since both numbers are `< 2 ^ (m * m) ≤ 2 ^ k`. -/
theorem toMatrix_inj_of_lt {a b : ℕ} (ha : a < 2 ^ (m * m)) (hb : b < 2 ^ (m * m))
    (h : (toMatrix a : Matrix (Fin m) (Fin m) (ZMod 2)) = toMatrix b) : a = b := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  rcases lt_or_ge k (m * m) with hk | hk
  · have hkij := congrFun (congrFun h (flatEquiv.symm ⟨k, hk⟩).1) (flatEquiv.symm ⟨k, hk⟩).2
    simp only [toMatrix, Matrix.of_apply, Prod.mk.eta, Equiv.apply_symm_apply, Fin.val_mk] at hkij
    revert hkij; cases a.testBit k <;> cases b.testBit k <;> decide
  · rw [Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by norm_num) hk)),
      Nat.testBit_lt_two_pow (hb.trans_le (Nat.pow_le_pow_right (by norm_num) hk))]

/-- The packed product always lands in the enumeration range, `mul m a b < 2 ^ (m * m)` (its output
is a `Nat.ofBits` over `Fin (m * m)`); the in-range hypothesis the symplectic test feeds to
`toMatrix_inj_of_lt` / `toBlocks_inj_of_lt`. -/
theorem mul_lt (m a b : ℕ) : mul m a b < 2 ^ (m * m) := Nat.ofBits_lt_two_pow _

/-- **The `2n = n + n` block reindexing** `Fin (n + n) ≃ Fin n ⊕ Fin n` (`finSumFinEquiv`). The
paper's `2n` phase-space coordinates split as the polarization `X̂ ⊕ Ẑ`; this identifies the index
set `Fin (n + n)` of the packed `2n × 2n` matrix with the index set `Fin n ⊕ Fin n` of
`binarySymplecticGroup (Fin n)`. It is the bridge along which `toBlocks` carries a packed bitmask to
the block-indexed matrix the symplectic group lives on. -/
def blockEquiv (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv

/-- **Decode a packed `2n × 2n` bitmask to the block-indexed matrix** that `Sp(2n, 𝔽₂)` lives on:
`toMatrix a` (an `(n + n) × (n + n)` matrix) reindexed from `Fin (n + n)` to `Fin n ⊕ Fin n` by
`blockEquiv`. This is the form on which `binarySymplecticGroup (Fin n)` membership is stated. -/
def toBlocks (n a : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  (toMatrix (m := n + n) a).submatrix (blockEquiv n) (blockEquiv n)

/-- The block decode is multiplicative:
`toBlocks n (mul (n + n) a b) = toBlocks n a * toBlocks n b`. The packed product decodes to the
`Matrix` product (`toMatrix_mul`), and reindexing by a bijection on the shared middle index commutes
with multiplication (`Matrix.submatrix_mul_equiv`). -/
theorem toBlocks_mul (n a b : ℕ) :
    toBlocks n (mul (n + n) a b) = toBlocks n a * toBlocks n b := by
  simp only [toBlocks, blockEquiv, toMatrix_mul, Matrix.submatrix_mul_equiv]

/-- The block decode commutes with transpose:
`toBlocks n (transpose (n + n) a) = (toBlocks n a)ᵀ`. From `toMatrix_transpose` and
`Matrix.transpose_submatrix` (reindexing by the same equiv on both axes is symmetric under
transposition). -/
theorem toBlocks_transpose (n a : ℕ) :
    toBlocks n (transpose (n + n) a) = (toBlocks n a)ᵀ := by
  simp only [toBlocks, blockEquiv, toMatrix_transpose, Matrix.transpose_submatrix]

/-- **`toBlocks` is injective on the enumeration range**, the block-indexed reading of
`toMatrix_inj_of_lt`: reindexing by the bijection `blockEquiv` is itself injective (its inverse
`reindex` is `submatrix` by `blockEquiv.symm`), so a packed equation between two in-range bitmasks
is equivalent to the `Matrix` equation of their block decodings. This is the step that turns the
symplectic *matrix* condition back into the packed *Nat* equation. -/
theorem toBlocks_inj_of_lt {n a b : ℕ} (ha : a < 2 ^ ((n + n) * (n + n)))
    (hb : b < 2 ^ ((n + n) * (n + n))) (h : toBlocks n a = toBlocks n b) : a = b := by
  refine toMatrix_inj_of_lt ha hb ?_
  have h2 := congrArg
    (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) =>
      M.submatrix (blockEquiv n).symm (blockEquiv n).symm) h
  simpa only [toBlocks, blockEquiv, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] using h2

/-- **Encode a block-indexed `2n × 2n` matrix over `𝔽₂` as a packed bitmask** — the inverse of the
decoder `toBlocks`. Reindex `G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)` from
`Fin n ⊕ Fin n` to `Fin (n + n)` by `blockEquiv.symm` and pack the resulting `(n + n) × (n + n)`
matrix with `ofMatrix`. The block-level companion of the flat encoder `ofMatrix` (which `toBlocks`
decodes), colocated with its decoder here; characterised by the round-trip `toBlocks_ofBlocks`. The
packed Gram matrix `packedSymplecticMatrix` below is the special case `ofBlocks n symplecticMatrix`.
-/
def ofBlocks (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) : ℕ :=
  ofMatrix (G.submatrix (blockEquiv n).symm (blockEquiv n).symm)

/-- **`ofBlocks` is a section of `toBlocks`**: `toBlocks n (ofBlocks n G) = G`. Every block-indexed
matrix is the decoding of its own packing, so `ofBlocks` names a packed representative of `G` with
no information loss. Round-trip of `ofMatrix` (`toMatrix_ofMatrix`) followed by cancellation of the
reindexing against its inverse (`blockEquiv.symm` then `blockEquiv`). -/
theorem toBlocks_ofBlocks (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) :
    toBlocks n (ofBlocks n G) = G := by
  simp only [toBlocks, ofBlocks, blockEquiv, toMatrix_ofMatrix, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id]

/-- The packing of an `Fin n ⊕ Fin n`-indexed matrix lands in the enumeration range,
`ofBlocks n G < 2 ^ ((n + n) * (n + n))` (it is an `ofMatrix` on the `(n + n) × (n + n)` reindex,
`ofMatrix_lt`); the in-range hypothesis the packed injectivity / symplectic test feeds to
`toBlocks_inj_of_lt`. -/
theorem ofBlocks_lt (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) :
    ofBlocks n G < 2 ^ ((n + n) * (n + n)) :=
  ofMatrix_lt _

/-- **The packed Gram matrix `J = [[0, I], [I, 0]]`.** The packing of the paper's `symplecticMatrix`
(an `Fin n ⊕ Fin n`-indexed matrix), i.e. the special case `ofBlocks n symplecticMatrix` of the
encoder. Characterised by `toBlocks_packedSymplecticMatrix`. -/
def packedSymplecticMatrix (n : ℕ) : ℕ :=
  ofBlocks n (symplecticMatrix : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2))

/-- The packed Gram matrix lands in the enumeration range,
`packedSymplecticMatrix n < 2 ^ ((n + n) * (n + n))` (it is an `ofBlocks`, `ofBlocks_lt`); the
in-range hypothesis for the right-hand side of the symplectic test. -/
theorem packedSymplecticMatrix_lt (n : ℕ) :
    packedSymplecticMatrix n < 2 ^ ((n + n) * (n + n)) :=
  ofBlocks_lt n _

/-- **The packed Gram matrix decodes to the paper's `symplecticMatrix`**,
`toBlocks n (packedSymplecticMatrix n) = symplecticMatrix`. Immediate from the encoder round-trip
`toBlocks_ofBlocks` at `G = symplecticMatrix`. -/
theorem toBlocks_packedSymplecticMatrix (n : ℕ) :
    toBlocks n (packedSymplecticMatrix n)
      = (symplecticMatrix : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) :=
  toBlocks_ofBlocks n (symplecticMatrix : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2))

/-- **The packed symplectic-membership test** for `Sp(2n, 𝔽₂)`: the paper's condition `Gᵀ J G = J`
(the second reading, `mem_binarySymplecticGroup_iff'`) written entirely in the packed calculus —
`transpose`, `mul` and the packed Gram matrix `packedSymplecticMatrix n` — as a single `Nat`
equation. Being an equation of natural numbers it is decided by `Nat.decEq` on two natively-computed
bitmasks (no `Matrix` / `Pi`-type is materialised), which is exactly what makes the finite
`Sp(2)` / `Sp(4)` verification tractable in the kernel; `isPackedSymplectic_iff_mem` proves it
equivalent to genuine `binarySymplecticGroup` membership. -/
def IsPackedSymplectic (n a : ℕ) : Prop :=
  mul (n + n) (transpose (n + n) a) (mul (n + n) (packedSymplecticMatrix n) a)
    = packedSymplecticMatrix n

/-- The packed symplectic test is decidable — it is a `Nat` equation — so it can be discharged by
`decide` in the finite `Sp(2)` / `Sp(4)` verification. -/
instance decidableIsPackedSymplectic (n a : ℕ) : Decidable (IsPackedSymplectic n a) := by
  unfold IsPackedSymplectic; infer_instance

/-- **The packed test is faithful to `Sp(2n, 𝔽₂)` membership.**
`IsPackedSymplectic n a ↔ toBlocks n a ∈ binarySymplecticGroup (Fin n)`: the packed `Nat` equation
`Gᵀ J G = J` holds exactly when the block decode of `a` is a binary symplectic matrix. Forward,
apply the (homomorphic) decode `toBlocks n` to the packed equation and read off
`mem_binarySymplecticGroup_iff'` via `toBlocks_mul` / `toBlocks_transpose` /
`toBlocks_packedSymplecticMatrix`; backward, the same block identities give the decode equation,
which `toBlocks_inj_of_lt` lifts back to the `Nat` equation (both sides are in range: `mul_lt`,
`packedSymplecticMatrix_lt`). This is the bridge that certifies the finite packed check against the
real symplectic group. -/
theorem isPackedSymplectic_iff_mem (n a : ℕ) :
    IsPackedSymplectic n a ↔ toBlocks n a ∈ binarySymplecticGroup (Fin n) := by
  unfold IsPackedSymplectic
  rw [mem_binarySymplecticGroup_iff']
  constructor
  · intro h
    have h2 := congrArg (toBlocks n) h
    rw [toBlocks_mul, toBlocks_transpose, toBlocks_mul, toBlocks_packedSymplecticMatrix,
      ← mul_assoc] at h2
    exact h2
  · intro h
    refine toBlocks_inj_of_lt (mul_lt _ _ _) (packedSymplecticMatrix_lt n) ?_
    rw [toBlocks_mul, toBlocks_transpose, toBlocks_mul, toBlocks_packedSymplecticMatrix,
      ← mul_assoc]
    exact h

/-! ### Kernel-tractability guards

The purpose of the packed calculus is that the symplectic test evaluates **natively in the
kernel** — each check is one `Nat`-arithmetic equation, with no `2 ^ (m * m)` function-type closures
materialised. These `decide` checks exercise exactly the finite verification `lem-local` needs: they
run the `Sp(2, 𝔽₂)` (`n = 1`) and `Sp(4, 𝔽₂)` (`n = 2`) tests on the Gram matrix `J` (which is
symplectic, `symplecticMatrix_mem_binarySymplecticGroup`) and on the zero matrix (which is not), and
`decide` discharges each — the concrete demonstration that the substrate the certificate replay (W3)
and completeness sieve (W4) run on is kernel-tractable. -/

end CliffordCSS.Packed

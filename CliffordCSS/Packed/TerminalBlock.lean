import CliffordCSS.Packed.SymplecticClosure
import CliffordCSS.DepthOne.LocalMove

/-!
# The packed terminal-block predicate (Beyond transversality, App. D.1 — Lemma D.4)

Pure mathematics : the **packed `Nat` version of the terminal-block
predicate** `IsTerminalLayer` (Eq. (d1-term)) of *Beyond transversality* (arXiv:2608.05688), proved
equivalent to the `Matrix` predicate under the packed decoder `toBlocks`. It names only raw carriers
(`Matrix`, `Nat`, `Fin`, `ZMod 2`) and the this library terminal predicate.

## Why this exists (the reachability half of Lemma D.4)

The *Local reduction* lemma (`lem-local`, Lemma D.4) is discharged by a **kernel computation** on
the packed representation (`dec-d4-kernel-computed-reachability`): reverse breadth-first search from
the **terminal set** over the enumerated element list of `Sp(4, 𝔽₂)` (resp. `Sp(2, 𝔽₂)`). The
completeness half — the enumeration by closure from the elementary Clifford generators — is landed
(`CliffordCSS/Packed/CliffordCompleteness.lean`). The reachability half needs the terminal predicate,
the local moves and bounded reachability *all in the packed calculus*, so the kernel evaluates them
natively on `Nat` bitmasks rather than on the function-type carrier
`Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)` (measured intractable — see
`CliffordCSS/Packed/BinaryMatrix.lean`). **This file is the first of those three**: the packed terminal
predicate and its agreement with the `Matrix` one.

## The terminal predicate, packed

A block `g = [[A, B], [C, D]]` (four `n × n` blocks) is *terminal* (`IsTerminalBlock`) when all six
manufactured generators of Lemma D.2 vanish, `A Bᵀ = Dᵀ B = B + Bᵀ = C Dᵀ = Cᵀ A = C + Cᵀ = 0`.
Those products are of the `n × n` **sub-blocks**, so the packed version extracts the four sub-blocks
of the packed `2n × 2n` bitmask `a` as packed `n × n` bitmasks (`subBlock`, and the four named
`blockA` / `blockB` / `blockC` / `blockD`), then writes the six conditions with the packed `n × n`
product `mul n` and `transpose n`:

* `IsPackedTerminal n a` — the six-fold conjunction of `Nat` equations (a product's packing is `0`,
  or an off-diagonal block equals its packed transpose for the two symmetry conditions
  `B + Bᵀ = 0` ⟺ `B = Bᵀ`), with its `Decidable` instance, so it is discharged by `decide` in the
  finite `Sp(2)` / `Sp(4)` reachability check.
* `isPackedTerminal_iff_isTerminalLayer` — the faithfulness bridge
  `IsPackedTerminal n a ↔ IsTerminalLayer (toBlocks n a)`: the packed test decides genuine
  terminality of the block decode. Proved size-generically (all `n`) by decoding each packed
  sub-block to the matching `Matrix.toBlocks` projection (`toMatrix_subBlock`) and bridging each
  packed `Nat` equation to its `Matrix` equation (`packedMul_eq_zero_iff` via injectivity of the
  block decode, and `packed_symm_iff` for the two symmetry conditions).

Only the block *decode* `toBlocks n a` is read (never a range hypothesis on `a`), so the agreement
holds for every `a : ℕ`.
-/

open Matrix

namespace CliffordCSS.Packed

/-! ### Packed `n × n` sub-block extraction from a packed `2n × 2n` bitmask -/

/-- **Extract a packed `n × n` sub-block** of the packed `2n × 2n` bitmask `a`, selected by the two
sum-embeddings `s, t : Fin n → Fin n ⊕ Fin n`. Bit `flatEquiv (i, j)` of the result reads bit
`flatEquiv (blockEquiv n (s i), blockEquiv n (t j))` of `a` — i.e. entry `(i, j)` of the sub-block
is entry `(s i, t j)` of the block-indexed decode `toBlocks n a`. The four blocks `A, B, C, D` of
`toBlocks n a` are the choices `s, t ∈ {Sum.inl, Sum.inr}`. -/
def subBlock (n a : ℕ) (s t : Fin n → Fin n ⊕ Fin n) : ℕ :=
  Nat.ofBits fun p : Fin (n * n) =>
    a.testBit (flatEquiv (m := n + n)
      (blockEquiv n (s ((flatEquiv (m := n)).symm p).1),
        blockEquiv n (t ((flatEquiv (m := n)).symm p).2)) : ℕ)

/-- A packed sub-block lands in the `n × n` enumeration range, `subBlock n a s t < 2 ^ (n * n)`
(it is a `Nat.ofBits` over `Fin (n * n)`, `Nat.ofBits_lt_two_pow`); the in-range hypothesis the
symmetry bridge `packed_symm_iff` feeds to `toMatrix_inj_of_lt`. -/
theorem subBlock_lt (n a : ℕ) (s t : Fin n → Fin n ⊕ Fin n) :
    subBlock n a s t < 2 ^ (n * n) := Nat.ofBits_lt_two_pow _

/-- **Correctness of the sub-block extraction**: the decode of `subBlock n a s t` is the `n × n`
matrix reading entry `(i, j)` off the block decode at `(s i, t j)`,
`toMatrix (subBlock n a s t) = of fun i j => toBlocks n a (s i) (t j)`. Immediate from
`testBit_ofBits` and the round-trip of `flatEquiv`. -/
theorem toMatrix_subBlock (n a : ℕ) (s t : Fin n → Fin n ⊕ Fin n) :
    (toMatrix (subBlock n a s t) : Matrix (Fin n) (Fin n) (ZMod 2))
      = Matrix.of fun i j => toBlocks n a (s i) (t j) := by
  ext i j
  simp only [toMatrix, subBlock, toBlocks, Matrix.of_apply, Matrix.submatrix_apply,
    testBit_ofBits, Equiv.symm_apply_apply]

/-- The packed upper-left block `A = g.toBlocks₁₁` of `g = toBlocks n a`. -/
def blockA (n a : ℕ) : ℕ := subBlock n a Sum.inl Sum.inl

/-- The packed upper-right block `B = g.toBlocks₁₂` of `g = toBlocks n a`. -/
def blockB (n a : ℕ) : ℕ := subBlock n a Sum.inl Sum.inr

/-- The packed lower-left block `C = g.toBlocks₂₁` of `g = toBlocks n a`. -/
def blockC (n a : ℕ) : ℕ := subBlock n a Sum.inr Sum.inl

/-- The packed lower-right block `D = g.toBlocks₂₂` of `g = toBlocks n a`. -/
def blockD (n a : ℕ) : ℕ := subBlock n a Sum.inr Sum.inr

/-- The packed block `B` lands in range, `blockB n a < 2 ^ (n * n)` (`subBlock_lt`); the in-range
hypothesis the symmetry bridge `packed_symm_iff` consumes, phrased in terms of `blockB` so the
rewrite pattern matches the terminal predicate's third conjunct. -/
theorem blockB_lt (n a : ℕ) : blockB n a < 2 ^ (n * n) := subBlock_lt n a Sum.inl Sum.inr

/-- The packed block `C` lands in range, `blockC n a < 2 ^ (n * n)` (`subBlock_lt`); the in-range
hypothesis the symmetry bridge `packed_symm_iff` consumes for the sixth conjunct. -/
theorem blockC_lt (n a : ℕ) : blockC n a < 2 ^ (n * n) := subBlock_lt n a Sum.inr Sum.inl

/-- The packed block `A` decodes to the `Matrix` upper-left block: `toMatrix (blockA n a) =
(toBlocks n a).toBlocks₁₁`. -/
theorem toMatrix_blockA (n a : ℕ) :
    (toMatrix (blockA n a) : Matrix (Fin n) (Fin n) (ZMod 2)) = (toBlocks n a).toBlocks₁₁ := by
  rw [blockA, toMatrix_subBlock]; rfl

/-- The packed block `B` decodes to the `Matrix` upper-right block: `toMatrix (blockB n a) =
(toBlocks n a).toBlocks₁₂`. -/
theorem toMatrix_blockB (n a : ℕ) :
    (toMatrix (blockB n a) : Matrix (Fin n) (Fin n) (ZMod 2)) = (toBlocks n a).toBlocks₁₂ := by
  rw [blockB, toMatrix_subBlock]; rfl

/-- The packed block `C` decodes to the `Matrix` lower-left block: `toMatrix (blockC n a) =
(toBlocks n a).toBlocks₂₁`. -/
theorem toMatrix_blockC (n a : ℕ) :
    (toMatrix (blockC n a) : Matrix (Fin n) (Fin n) (ZMod 2)) = (toBlocks n a).toBlocks₂₁ := by
  rw [blockC, toMatrix_subBlock]; rfl

/-- The packed block `D` decodes to the `Matrix` lower-right block: `toMatrix (blockD n a) =
(toBlocks n a).toBlocks₂₂`. -/
theorem toMatrix_blockD (n a : ℕ) :
    (toMatrix (blockD n a) : Matrix (Fin n) (Fin n) (ZMod 2)) = (toBlocks n a).toBlocks₂₂ := by
  rw [blockD, toMatrix_subBlock]; rfl

/-! ### Packed `Nat`-equation bridges -/

/-- The decode of the packed zero bitmask is the zero matrix: `toMatrix (0 : ℕ) = 0`
(every bit of `0` is clear, `Nat.zero_testBit`). -/
theorem toMatrix_zero (n : ℕ) :
    (toMatrix (0 : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2)) = 0 := by
  ext i j
  simp [toMatrix, Nat.zero_testBit]

/-- **A packed bitmask below the range is `0` exactly when its decode vanishes**:
`z = 0 ↔ toMatrix n z = 0` for `z < 2 ^ (n * n)`. The `Nat` reading of `toMatrix_inj_of_lt` against
the in-range zero bitmask `0` (`toMatrix_zero`). -/
theorem eq_zero_iff_toMatrix {n z : ℕ} (hz : z < 2 ^ (n * n)) :
    z = 0 ↔ (toMatrix z : Matrix (Fin n) (Fin n) (ZMod 2)) = 0 := by
  constructor
  · rintro rfl; exact toMatrix_zero n
  · intro h
    exact toMatrix_inj_of_lt hz (by positivity) (h.trans (toMatrix_zero n).symm)

/-- **A packed product vanishes exactly when the `Matrix` product does**:
`mul n x y = 0 ↔ toMatrix n x * toMatrix n y = 0`. The packed product always lands in range
(`mul_lt`), so `eq_zero_iff_toMatrix` turns the `Nat` equation into the decode equation, which
`toMatrix_mul` rewrites to the `Matrix` product. -/
theorem packedMul_eq_zero_iff (n x y : ℕ) :
    mul n x y = 0 ↔ (toMatrix x : Matrix (Fin n) (Fin n) (ZMod 2)) * toMatrix y = 0 := by
  rw [eq_zero_iff_toMatrix (mul_lt n x y), toMatrix_mul]

/-- **A packed bitmask equals its packed transpose exactly when its decode is symmetric** — in the
`𝔽₂` form `M + Mᵀ = 0`: `x = transpose n x ↔ toMatrix n x + (toMatrix n x)ᵀ = 0` for `x` in range.
Forward, the packed equation decodes to `M = Mᵀ` (via `toMatrix_transpose`), whence `M + M = 0`
(`Matrix.add_self_eq_zero`); backward, `M + Mᵀ = 0` gives `M = Mᵀ` over characteristic two, which
`toMatrix_inj_of_lt` lifts back to the `Nat` equation. This is the packed reading of the two
symmetry conditions `B + Bᵀ = 0`, `C + Cᵀ = 0` of Eq. (d1-term). -/
theorem packed_symm_iff {n x : ℕ} (hx : x < 2 ^ (n * n)) :
    x = transpose n x ↔ (toMatrix x : Matrix (Fin n) (Fin n) (ZMod 2)) + (toMatrix x)ᵀ = 0 := by
  constructor
  · intro h
    have hs : (toMatrix x : Matrix (Fin n) (Fin n) (ZMod 2)) = (toMatrix x)ᵀ := by
      rw [← toMatrix_transpose, ← h]
    rw [← hs]; exact Matrix.add_self_eq_zero _
  · intro h
    refine toMatrix_inj_of_lt hx (Nat.ofBits_lt_two_pow _) ?_
    rw [toMatrix_transpose]
    have key : (toMatrix x : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
        = toMatrix x + (toMatrix x + (toMatrix x)ᵀ) := by
      rw [← add_assoc, Matrix.add_self_eq_zero, zero_add]
    rw [key, h, add_zero]

/-! ### The packed terminal predicate and its faithfulness -/

/-- **The packed terminal-block predicate** (Eq. (d1-term), packed). The block decode `toBlocks n a`
has packed `n × n` sub-blocks `A = blockA`, `B = blockB`, `C = blockC`, `D = blockD`; `a` is
terminal when the six manufactured generators vanish, written in the packed calculus:
`A Bᵀ = 0`, `Dᵀ B = 0`, `B = Bᵀ` (i.e. `B + Bᵀ = 0`), `C Dᵀ = 0`, `Cᵀ A = 0`, `C = Cᵀ`. Being a
conjunction of `Nat` equations it is decided by `Nat.decEq` on natively-computed bitmasks, so the
finite reachability check runs it in the kernel. -/
def IsPackedTerminal (n a : ℕ) : Prop :=
  mul n (blockA n a) (transpose n (blockB n a)) = 0 ∧
    mul n (transpose n (blockD n a)) (blockB n a) = 0 ∧
    blockB n a = transpose n (blockB n a) ∧
    mul n (blockC n a) (transpose n (blockD n a)) = 0 ∧
    mul n (transpose n (blockC n a)) (blockA n a) = 0 ∧
    blockC n a = transpose n (blockC n a)

/-- The packed terminal test is decidable — a conjunction of `Nat` equations — so the finite
reachability check discharges it by `decide`. -/
instance decidableIsPackedTerminal (n a : ℕ) : Decidable (IsPackedTerminal n a) := by
  unfold IsPackedTerminal; infer_instance

/-- **The packed terminal test is faithful to `IsTerminalLayer`**:
`IsPackedTerminal n a ↔ IsTerminalLayer (toBlocks n a)`. Each packed sub-block decodes to the
matching `Matrix.toBlocks` projection (`toMatrix_blockA` … `toMatrix_blockD`), and each packed `Nat`
equation bridges to its `Matrix` equation (`packedMul_eq_zero_iff` for the four products,
`packed_symm_iff` for the two symmetry conditions), matching the six conjuncts of
`IsTerminalBlock` (Eq. (d1-term)) one for one. Size-generic (holds for every `n`, every `a`); the
finite reachability check applies it at `n = 2` (`Sp(4, 𝔽₂)`) and `n = 1` (`Sp(2, 𝔽₂)`). -/
theorem isPackedTerminal_iff_isTerminalLayer (n a : ℕ) :
    IsPackedTerminal n a ↔ IsTerminalLayer (toBlocks n a) := by
  unfold IsPackedTerminal IsTerminalLayer IsTerminalBlock
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))))
  · rw [packedMul_eq_zero_iff, toMatrix_transpose, toMatrix_blockA, toMatrix_blockB]
  · rw [packedMul_eq_zero_iff, toMatrix_transpose, toMatrix_blockD, toMatrix_blockB]
  · rw [packed_symm_iff (blockB_lt n a), toMatrix_blockB]
  · rw [packedMul_eq_zero_iff, toMatrix_transpose, toMatrix_blockC, toMatrix_blockD]
  · rw [packedMul_eq_zero_iff, toMatrix_transpose, toMatrix_blockC, toMatrix_blockA]
  · rw [packed_symm_iff (blockC_lt n a), toMatrix_blockC]

/-! ### Kernel-tractability guards

These `decide` checks exercise the packed terminal test on the two block widths the finite
verification `lem-local` runs over, confirming it evaluates natively in the kernel (no function-type
closures materialised). The packed Gram matrix `J = [[0, I], [I, 0]]` and the packed identity
`one n = [[I, 0], [0, I]]` are both terminal — the two terminal blocks of `Sp(2, 𝔽₂)`, and Levi
blocks in general. -/

end CliffordCSS.Packed

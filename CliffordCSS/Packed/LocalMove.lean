import CliffordCSS.Packed.TerminalBlock

/-!
# The packed local-move parameter formulas (Beyond transversality, App. D.1 — Lemma D.4)

Pure mathematics : the **packed `Nat` version of the local-move
parameter formulas** `S^Z(g, ε)` / `S^X(g, ε)` (Eq. (d1-eps)) of *Beyond transversality*
(arXiv:2608.05688), proved equal — under the packed decoder `toBlocks` — to the `Matrix` parameter
formulas `layerZParam` / `layerXParam`. It names only raw carriers (`Matrix`, `Nat`, `Fin`,
`ZMod 2`) and the this library parameter functions.

## Why this exists (the reachability half of Lemma D.4)

The *Local reduction* lemma (`lem-local`, Lemma D.4) is discharged by a **kernel computation** on
the packed representation (`dec-d4-kernel-computed-reachability`): reverse breadth-first search from
the terminal set over the enumerated element list of `Sp(4, 𝔽₂)` (resp. `Sp(2, 𝔽₂)`). The
completeness half — the enumeration by closure from the elementary Clifford generators — is landed
(`CliffordCSS/Packed/CliffordCompleteness.lean`); the reachability half needs the terminal predicate,
the local **moves** and bounded reachability *all in the packed calculus*, so the kernel evaluates
them natively on `Nat` bitmasks rather than on the function-type carrier
`Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)` (measured intractable — see
`CliffordCSS/Packed/BinaryMatrix.lean`). The packed terminal predicate (`IsPackedTerminal`) is landed
(`CliffordCSS/Packed/TerminalBlock.lean`); **this file is the next ingredient of the moves**: the packed
parameter formulas, out of which each move's shear is manufactured.

## The parameter span, packed

A move (Eq. (d1-moves), `IsBlockMove`) from a block `g = [[A, B], [C, D]]` is a left/right
multiplication by the shear `U_Z(S)` / `L_X(T)` of a **nonzero** parameter `S ∈ Θ^Z(g)` /
`T ∈ Θ^X(g)`, where the two manufactured spans of Lemma D.2 are enumerated by a coefficient vector
`ε ∈ 𝔽₂³` through
`S^Z(g, ε) = ε₁·A Bᵀ + ε₂·Dᵀ B + ε₃·(B + Bᵀ)` (`layerZParam`) and its `X ↔ Z` dual
`S^X(g, ε) = ε₁·C Dᵀ + ε₂·Cᵀ A + ε₃·(C + Cᵀ)` (`layerXParam`). Both are **sums** of `𝔽₂` matrices,
so packing them needs the packed `𝔽₂` matrix sum, the last missing operation of the packed calculus
(which already carries `mul`, `transpose`, `one`):

* `add` — the packed `𝔽₂` matrix sum, entrywise `xor` of the two bitmasks (matrix addition over
  characteristic two), with `toMatrix_add` and the range bound `add_lt`.
* `packedSmul` — the `𝔽₂` scalar action `c • x` on a packed bitmask (`x` when `c = 1`, `0` when
  `c = 0`), with `toMatrix_packedSmul`.
* `packedLayerZParam` / `packedLayerXParam` — the packed parameter formulas, the `ε`-combination of
  the three packed generators read off the packed sub-blocks (`blockA` … `blockD`,
  `CliffordCSS/Packed/TerminalBlock.lean`) with `mul`, `transpose`, `add`; and their faithfulness
  bridges `toMatrix_packedLayerZParam` / `toMatrix_packedLayerXParam`
  (`toMatrix (packedLayerZParam n a ε) = layerZParam (toBlocks n a) ε`) and the nonzero-agreement
  corollaries `packedLayerZParam_eq_zero_iff` / `packedLayerXParam_eq_zero_iff` (the packed
  parameter vanishes exactly when the `Matrix` one does — the "nonzero parameter" filter each move
  applies). Size-generic (all `n`, all `a`); the finite reachability check applies them at `n = 2`
  (`Sp(4, 𝔽₂)`) and `n = 1` (`Sp(2, 𝔽₂)`).

Only the block *decode* `toBlocks n a` is read (never a range hypothesis on `a`), so every agreement
holds for every `a : ℕ`. The packed shears and the packed `IsBlockMove` relation these parameters
feed into are the next chunk.
-/

open Matrix

namespace CliffordCSS.Packed

variable {m : ℕ}

/-! ### Packed `𝔽₂` matrix addition -/

/-- **Packed `𝔽₂` matrix addition.** The bitmask whose bit `flatEquiv (i, j)` is the `xor` of that
bit of `a` and of `b` — matrix addition over characteristic two is entrywise `xor`. Every output bit
is a native `Nat.testBit` read (no `Matrix`/`Pi`-type value materialised); proved equal to the
`Matrix` sum `toMatrix a + toMatrix b` by `toMatrix_add`. Completes the packed `𝔽₂` matrix algebra
alongside `mul` and `transpose`; the packed parameter formulas below are its first consumer. -/
def add (m a b : ℕ) : ℕ :=
  Nat.ofBits fun p : Fin (m * m) => xor (a.testBit (p : ℕ)) (b.testBit (p : ℕ))

/-- **Correctness of the packed addition**: decoding `add m a b` yields the sum of the decodings,
`toMatrix (add m a b) = toMatrix a + toMatrix b`. The `(i, j)` decoded bit of `add m a b` is, by
`testBit_ofBits`, the `xor` of the `(i, j)` bits of `a` and `b`; over `ZMod 2` the indicator of a
`xor` is the sum of the two indicators (`0/1` case check). -/
theorem toMatrix_add (a b : ℕ) :
    (toMatrix (add m a b) : Matrix (Fin m) (Fin m) (ZMod 2)) = toMatrix a + toMatrix b := by
  ext i j
  simp only [add, toMatrix, Matrix.add_apply, Matrix.of_apply, testBit_ofBits]
  cases a.testBit (flatEquiv (i, j) : ℕ) <;> cases b.testBit (flatEquiv (i, j) : ℕ) <;> decide

/-- The packed sum always lands in the enumeration range, `add m a b < 2 ^ (m * m)` (its output is a
`Nat.ofBits` over `Fin (m * m)`, `Nat.ofBits_lt_two_pow`); the in-range hypothesis the parameter's
vanishing bridge feeds to `eq_zero_iff_toMatrix`. -/
theorem add_lt (m a b : ℕ) : add m a b < 2 ^ (m * m) := Nat.ofBits_lt_two_pow _

/-! ### The `𝔽₂` scalar action on a packed bitmask -/

/-- **The `𝔽₂` scalar action on a packed bitmask**: `c • x` is `x` when `c = 1` and `0` when `c = 0`
(over `ZMod 2` there are no other scalars). Used to weight each generator of the parameter span by a
coefficient of the vector `ε ∈ 𝔽₂³`. -/
def packedSmul (c : ZMod 2) (x : ℕ) : ℕ := if c = 1 then x else 0

/-- **Correctness of the packed scalar action**: `toMatrix (packedSmul c x) = c • toMatrix x`. By
the two-element case split on `c ∈ ZMod 2`: at `c = 1` the packing is `x` and `1 • M = M`; at
`c = 0` it is `0`, decoding to the zero matrix (`toMatrix_zero`), and `0 • M = 0`. -/
theorem toMatrix_packedSmul (c : ZMod 2) (x : ℕ) :
    (toMatrix (packedSmul c x) : Matrix (Fin m) (Fin m) (ZMod 2)) = c • toMatrix x := by
  rcases (show ∀ d : ZMod 2, d = 0 ∨ d = 1 from by decide) c with rfl | rfl
  · rw [packedSmul, if_neg (by decide), toMatrix_zero, zero_smul]
  · rw [packedSmul, if_pos rfl, one_smul]

/-! ### The packed `Z`-parameter formula -/

/-- **The packed `Z`-parameter formula** `S^Z(g, ε) = ε₁·A Bᵀ + ε₂·Dᵀ B + ε₃·(B + Bᵀ)`
(Eq. (d1-eps)), read off the packed sub-blocks `A = blockA`, `B = blockB`, `D = blockD` of the block
decode `toBlocks n a`, weighted by the coefficient vector `ε ∈ 𝔽₂³` and summed with the packed
calculus `mul` / `transpose` / `add`. As `ε` ranges over `𝔽₂³` its decodes are exactly the
manufactured span `Θ^Z(toBlocks n a)` of Lemma D.2. -/
def packedLayerZParam (n a : ℕ) (ε : Fin 3 → ZMod 2) : ℕ :=
  add n
    (add n (packedSmul (ε 0) (mul n (blockA n a) (transpose n (blockB n a))))
      (packedSmul (ε 1) (mul n (transpose n (blockD n a)) (blockB n a))))
    (packedSmul (ε 2) (add n (blockB n a) (transpose n (blockB n a))))

/-- **The packed `Z`-parameter is faithful to `layerZParam`**:
`toMatrix (packedLayerZParam n a ε) = layerZParam (toBlocks n a) ε`. Each packed operation decodes
to its `Matrix` counterpart (`toMatrix_add`, `toMatrix_packedSmul`, `toMatrix_mul`,
`toMatrix_transpose`) and each packed sub-block to the matching `Matrix.toBlocks` projection
(`toMatrix_blockA` … `toMatrix_blockD`), matching `spzParam` (Eq. (d1-eps)) term for term. -/
theorem toMatrix_packedLayerZParam (n a : ℕ) (ε : Fin 3 → ZMod 2) :
    (toMatrix (packedLayerZParam n a ε) : Matrix (Fin n) (Fin n) (ZMod 2))
      = layerZParam (toBlocks n a) ε := by
  rw [packedLayerZParam, layerZParam, spzParam]
  simp only [toMatrix_add, toMatrix_packedSmul, toMatrix_mul, toMatrix_transpose, toMatrix_blockA,
    toMatrix_blockB, toMatrix_blockD]

/-- The packed `Z`-parameter lands in the `n × n` enumeration range,
`packedLayerZParam n a ε < 2 ^ (n * n)` (a top-level `add`, `add_lt`); the in-range hypothesis the
vanishing bridge feeds to `eq_zero_iff_toMatrix`. -/
theorem packedLayerZParam_lt (n a : ℕ) (ε : Fin 3 → ZMod 2) :
    packedLayerZParam n a ε < 2 ^ (n * n) := add_lt _ _ _

/-- **The packed `Z`-parameter vanishes exactly when the `Matrix` one does**:
`packedLayerZParam n a ε = 0 ↔ layerZParam (toBlocks n a) ε = 0`. The packed value is in range
(`packedLayerZParam_lt`), so `eq_zero_iff_toMatrix` turns the `Nat` equation into the decode
equation, which `toMatrix_packedLayerZParam` rewrites to the `Matrix` parameter. This is the
"nonzero parameter" test each `Z`-move applies. -/
theorem packedLayerZParam_eq_zero_iff (n a : ℕ) (ε : Fin 3 → ZMod 2) :
    packedLayerZParam n a ε = 0 ↔ layerZParam (toBlocks n a) ε = 0 := by
  rw [eq_zero_iff_toMatrix (packedLayerZParam_lt n a ε), toMatrix_packedLayerZParam]

/-! ### The packed `X`-parameter formula (the `X ↔ Z` dual) -/

/-- **The packed `X`-parameter formula** `S^X(g, ε) = ε₁·C Dᵀ + ε₂·Cᵀ A + ε₃·(C + Cᵀ)`
(Eq. (d1-eps)), the `X ↔ Z` dual of `packedLayerZParam`, read off the packed sub-blocks
`A = blockA`, `C = blockC`, `D = blockD` of `toBlocks n a`. Its `ε`-decodes are the manufactured
span `Θ^X(toBlocks n a)` of Lemma D.2. -/
def packedLayerXParam (n a : ℕ) (ε : Fin 3 → ZMod 2) : ℕ :=
  add n
    (add n (packedSmul (ε 0) (mul n (blockC n a) (transpose n (blockD n a))))
      (packedSmul (ε 1) (mul n (transpose n (blockC n a)) (blockA n a))))
    (packedSmul (ε 2) (add n (blockC n a) (transpose n (blockC n a))))

/-- **The packed `X`-parameter is faithful to `layerXParam`** (dual to
`toMatrix_packedLayerZParam`):
`toMatrix (packedLayerXParam n a ε) = layerXParam (toBlocks n a) ε`. -/
theorem toMatrix_packedLayerXParam (n a : ℕ) (ε : Fin 3 → ZMod 2) :
    (toMatrix (packedLayerXParam n a ε) : Matrix (Fin n) (Fin n) (ZMod 2))
      = layerXParam (toBlocks n a) ε := by
  rw [packedLayerXParam, layerXParam, spxParam]
  simp only [toMatrix_add, toMatrix_packedSmul, toMatrix_mul, toMatrix_transpose, toMatrix_blockA,
    toMatrix_blockC, toMatrix_blockD]

/-- The packed `X`-parameter lands in the `n × n` enumeration range,
`packedLayerXParam n a ε < 2 ^ (n * n)` (a top-level `add`, `add_lt`). -/
theorem packedLayerXParam_lt (n a : ℕ) (ε : Fin 3 → ZMod 2) :
    packedLayerXParam n a ε < 2 ^ (n * n) := add_lt _ _ _

/-- **The packed `X`-parameter vanishes exactly when the `Matrix` one does** (dual to
`packedLayerZParam_eq_zero_iff`):
`packedLayerXParam n a ε = 0 ↔ layerXParam (toBlocks n a) ε = 0`. -/
theorem packedLayerXParam_eq_zero_iff (n a : ℕ) (ε : Fin 3 → ZMod 2) :
    packedLayerXParam n a ε = 0 ↔ layerXParam (toBlocks n a) ε = 0 := by
  rw [eq_zero_iff_toMatrix (packedLayerXParam_lt n a ε), toMatrix_packedLayerXParam]

/-! ### Kernel-tractability guards

These `decide` checks exercise the packed parameter formulas natively at the two block widths the
finite verification `lem-local` runs over, confirming a single parameter computation evaluates in
the kernel on `Nat` bitmasks (no function-type closures materialised). The packed Gram matrix
`J = [[0, I], [I, 0]]` is terminal, so every parameter available at it vanishes (Eq. (d1-term)); the
non-terminal block `[[1, 1], [0, 1]]` has `A Bᵀ = 1 ≠ 0`, witnessed by `ε = (1, 0, 0)`. -/

end CliffordCSS.Packed

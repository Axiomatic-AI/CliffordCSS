import CliffordCSS.Packed.LocalMove
import CliffordCSS.DepthOne.ShearLevi

/-!
# The packed local moves (Beyond transversality, App. D.1 — Lemma D.4)

Pure mathematics : the **packed `Nat` version of the local moves**
(Eq. (d1-moves), `IsBlockMove`) of *Beyond transversality* (arXiv:2608.05688) — the packed shears
`U_Z(S)` / `L_X(T)` and the finite neighbour list a block reaches by one move — proved *sound*
against the `Matrix` move relation under the packed decoder `toBlocks`. It names only raw carriers
(`Matrix`, `Nat`, `Fin`, `ZMod 2`) and the this library move relation `IsBlockMove` / the shears
`shearZ` / `shearX`.

## Why this exists (the reachability half of Lemma D.4)

The *Local reduction* lemma (`lem-local`, Lemma D.4) is discharged by a **kernel computation** on
the packed representation (`dec-d4-kernel-computed-reachability`): reverse breadth-first search from
the terminal set over the enumerated element list of `Sp(4, 𝔽₂)` (resp. `Sp(2, 𝔽₂)`). The
completeness half is landed (`CliffordCSS/Packed/CliffordCompleteness.lean`); the reachability half
needs the terminal predicate, the local **moves** and bounded reachability *all in the packed
calculus*, so the kernel evaluates them natively on `Nat` bitmasks rather than on the function-type
carrier
`Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)` (measured intractable — see
`CliffordCSS/Packed/BinaryMatrix.lean`). The packed terminal predicate (`IsPackedTerminal`,
`CliffordCSS/Packed/TerminalBlock.lean`) and the packed parameter formulas (`packedLayerZParam` /
`packedLayerXParam`, `CliffordCSS/Packed/LocalMove.lean`) are landed; **this file assembles the moves**.

## The moves, packed

A move (Eq. (d1-moves)) from a block `g = toBlocks n a` is a left/right multiplication by the shear
`U_Z(S)` / `L_X(T)` of a **nonzero** parameter `S = S^Z(g, ε)` / `T = S^X(g, ε)` (`ε ∈ 𝔽₂³`). The
shears are `2n × 2n` block matrices `U_Z(S) = [[I, S], [0, I]]`, `L_X(T) = [[I, 0], [T, I]]`, so the
packed version builds them **directly as `2n × 2n` bitmasks** (no `toMatrix` / `ofMatrix` in the
computational path, keeping the eventual kernel BFS `decide` tractable):

* `packedShearZ` / `packedShearX` — the packed shears, with the block-decode bridges
  `toBlocks_packedShearZ` / `toBlocks_packedShearX`
  (`toBlocks n (packedShearZ n s) = shearZ (toMatrix s)`) and range bounds.
* `packedNeighbors n a` — the **finite list of one-move targets** of `a`: for each `ε ∈ 𝔽₂³` with a
  nonzero packed parameter, the two `Z`-shear products (left `U_Z(S) · a`, right `a · U_Z(S)`) and,
  for a nonzero `X`-parameter, the two `X`-shear products — at most `28` targets, every one computed
  by the packed product `mul (n + n)`. A `List` (not an existential) so the packed bounded
  reachability of the next chunk is `Decidable` by `decide`.
* `packedNeighbors_sound` — the **soundness bridge**: every `a' ∈ packedNeighbors n a` is a genuine
  move, `IsBlockMove (toBlocks n a) (toBlocks n a')`. Each list entry is a packed shear-product, so
  `toBlocks_mul` + the shear bridge decode it to `shearZ (layerZParam (toBlocks n a) ε) · toBlocks n
  a` (or the right/`X` variant), and the nonzero filter gives the `≠ 0` side condition
  (`packedLayerZParam_eq_zero_iff`). This is the direction the next chunk's
  `packedReaches k a → ReachesTerminalIn k (toBlocks n a)` consumes.

Only the block *decode* `toBlocks n a` is read (never a range hypothesis on `a`), so soundness holds
for every `a : ℕ`; the finite reachability check applies it at `n = 2` (`Sp(4, 𝔽₂)`) and `n = 1`
(`Sp(2, 𝔽₂)`).
-/

open Matrix

namespace CliffordCSS.Packed

/-! ### The packed shears `U_Z(S)` and `L_X(T)` -/

/-- **The packed `Z`-shear** `U_Z(S) = [[I, S], [0, I]]` (Convention c7), built directly as a packed
`2n × 2n` bitmask from a packed `n × n` parameter `s`: bit `flatEquiv (I, J)` reads, after decoding
`I, J : Fin (n + n)` to sum coordinates `X, Y : Fin n ⊕ Fin n`, the identity on the diagonal blocks
(`X, Y` both `inl` or both `inr`), the parameter `s` on the upper-right block (`X = inl`,
`Y = inr`), and `0` on the lower-left block. Pure `Nat` bit-reads (no `Matrix` / `Pi`-type); proved
equal to `shearZ (toMatrix s)` under the block decoder by `toBlocks_packedShearZ`. -/
def packedShearZ (n s : ℕ) : ℕ :=
  Nat.ofBits fun p : Fin ((n + n) * (n + n)) =>
    match (blockEquiv n).symm ((flatEquiv (m := n + n)).symm p).1,
        (blockEquiv n).symm ((flatEquiv (m := n + n)).symm p).2 with
    | Sum.inl i, Sum.inl j => decide (i = j)
    | Sum.inl i, Sum.inr j => s.testBit (flatEquiv (m := n) (i, j) : ℕ)
    | Sum.inr _, Sum.inl _ => false
    | Sum.inr i, Sum.inr j => decide (i = j)

/-- **The packed `X`-shear** `L_X(T) = [[I, 0], [T, I]]` (the `X ↔ Z` dual of `packedShearZ`), built
directly as a packed `2n × 2n` bitmask: identity on the diagonal blocks, `0` on the upper-right
block, the parameter `t` on the lower-left block (`X = inr`, `Y = inl`). Proved equal to
`shearX (toMatrix t)` by `toBlocks_packedShearX`. -/
def packedShearX (n t : ℕ) : ℕ :=
  Nat.ofBits fun p : Fin ((n + n) * (n + n)) =>
    match (blockEquiv n).symm ((flatEquiv (m := n + n)).symm p).1,
        (blockEquiv n).symm ((flatEquiv (m := n + n)).symm p).2 with
    | Sum.inl i, Sum.inl j => decide (i = j)
    | Sum.inl _, Sum.inr _ => false
    | Sum.inr i, Sum.inl j => t.testBit (flatEquiv (m := n) (i, j) : ℕ)
    | Sum.inr i, Sum.inr j => decide (i = j)


/-- **The packed `Z`-shear is faithful to `shearZ`**:
`toBlocks n (packedShearZ n s) = shearZ (toMatrix s)`. Read entry `(X, Y)` of the block decode: it
is bit `flatEquiv (blockEquiv X, blockEquiv Y)` of `packedShearZ n s`, which `testBit_ofBits` and
the `flatEquiv` / `blockEquiv` round-trips reduce to the `(X, Y)` case of the defining `match`; that
matches `fromBlocks 1 (toMatrix s) 0 1 X Y` block for block (`Matrix.one_apply` on the diagonal, the
decode `toMatrix s` on the upper-right, `0` on the lower-left). -/
theorem toBlocks_packedShearZ (n s : ℕ) :
    toBlocks n (packedShearZ n s) = shearZ (toMatrix s) := by
  ext X Y
  simp only [toBlocks, Matrix.submatrix_apply, toMatrix, Matrix.of_apply, packedShearZ,
    testBit_ofBits, Equiv.symm_apply_apply, shearZ]
  cases X <;> cases Y <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.of_apply,
      decide_eq_true_eq, Bool.false_eq_true, if_false]

/-- **The packed `X`-shear is faithful to `shearX`** (dual to `toBlocks_packedShearZ`):
`toBlocks n (packedShearX n t) = shearX (toMatrix t)`. -/
theorem toBlocks_packedShearX (n t : ℕ) :
    toBlocks n (packedShearX n t) = shearX (toMatrix t) := by
  ext X Y
  simp only [toBlocks, Matrix.submatrix_apply, toMatrix, Matrix.of_apply, packedShearX,
    testBit_ofBits, Equiv.symm_apply_apply, shearX]
  cases X <;> cases Y <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.of_apply,
      decide_eq_true_eq, Bool.false_eq_true, if_false]

/-! ### Decode bridges for a packed shear-move -/

/-- **Decode a left `Z`-shear move**:
`toBlocks n (mul (n + n) (packedShearZ n s) a) = shearZ (toMatrix s) * toBlocks n a`. The packed
product decodes to the `Matrix` product (`toBlocks_mul`) and the shear to `shearZ (toMatrix s)`
(`toBlocks_packedShearZ`). -/
theorem toBlocks_mul_packedShearZ_left (n a s : ℕ) :
    toBlocks n (mul (n + n) (packedShearZ n s) a) = shearZ (toMatrix s) * toBlocks n a := by
  rw [toBlocks_mul, toBlocks_packedShearZ]

/-- **Decode a right `Z`-shear move**:
`toBlocks n (mul (n + n) a (packedShearZ n s)) = toBlocks n a * shearZ (toMatrix s)`. -/
theorem toBlocks_mul_packedShearZ_right (n a s : ℕ) :
    toBlocks n (mul (n + n) a (packedShearZ n s)) = toBlocks n a * shearZ (toMatrix s) := by
  rw [toBlocks_mul, toBlocks_packedShearZ]

/-- **Decode a left `X`-shear move**:
`toBlocks n (mul (n + n) (packedShearX n t) a) = shearX (toMatrix t) * toBlocks n a`. -/
theorem toBlocks_mul_packedShearX_left (n a t : ℕ) :
    toBlocks n (mul (n + n) (packedShearX n t) a) = shearX (toMatrix t) * toBlocks n a := by
  rw [toBlocks_mul, toBlocks_packedShearX]

/-- **Decode a right `X`-shear move**:
`toBlocks n (mul (n + n) a (packedShearX n t)) = toBlocks n a * shearX (toMatrix t)`. -/
theorem toBlocks_mul_packedShearX_right (n a t : ℕ) :
    toBlocks n (mul (n + n) a (packedShearX n t)) = toBlocks n a * shearX (toMatrix t) := by
  rw [toBlocks_mul, toBlocks_packedShearX]

/-! ### The packed neighbour list and its soundness -/

/-- The eight coefficient vectors `ε ∈ 𝔽₂³` enumerating the two parameter spans `Θ^Z` / `Θ^X` of
Lemma D.2. The zero vector yields the zero parameter (a trivial `U_Z(0) = I` self-loop) and is
filtered out by the nonzero guard of `packedNeighbors`; the remaining seven per family give the span
elements, so the list is complete for the reachability search. -/
def epsList : List (Fin 3 → ZMod 2) :=
  [![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

/-- **The packed one-move neighbour list of `a`.** For each `ε ∈ 𝔽₂³` (`epsList`): if the packed
`Z`-parameter `S = packedLayerZParam n a ε` is nonzero, the two `Z`-shear products
`U_Z(S) · a = mul (n + n) (packedShearZ n S) a` and `a · U_Z(S) = mul (n + n) a (packedShearZ n S)`;
and, if the packed `X`-parameter `T` is nonzero, the two `X`-shear products. At most `28` entries
(seven nonzero `ε` per family, two sides each), every one a packed product `mul (n + n)`. Being a
`List` it is decidably searchable, which makes the packed bounded reachability of the next chunk
`Decidable` by `decide`. -/
def packedNeighbors (n a : ℕ) : List ℕ :=
  epsList.flatMap fun ε =>
    (if packedLayerZParam n a ε ≠ 0 then
        [mul (n + n) (packedShearZ n (packedLayerZParam n a ε)) a,
          mul (n + n) a (packedShearZ n (packedLayerZParam n a ε))]
      else []) ++
    (if packedLayerXParam n a ε ≠ 0 then
        [mul (n + n) (packedShearX n (packedLayerXParam n a ε)) a,
          mul (n + n) a (packedShearX n (packedLayerXParam n a ε))]
      else [])

/-- Membership in a guarded two-element list: if `a' ∈ (if P then [x, y] else [])` then `P` holds
and `a'` is `x` or `y`. Used by `packedNeighbors_sound` on each family's guarded pair. -/
private theorem mem_guarded_pair {P : Prop} [Decidable P] {x y a' : ℕ}
    (h : a' ∈ (if P then [x, y] else [])) : P ∧ (a' = x ∨ a' = y) := by
  by_cases hP : P
  · rw [if_pos hP] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    exact ⟨hP, h⟩
  · rw [if_neg hP] at h
    simp only [List.not_mem_nil] at h

/-- **Soundness of the packed neighbour list**: every one-move target is a genuine move,
`a' ∈ packedNeighbors n a → IsBlockMove (toBlocks n a) (toBlocks n a')`. From `List.mem_flatMap`
pick the witnessing `ε`; the guard `mem_guarded_pair` gives the nonzero packed parameter and finds
`a'` as one of the four shear products. Each decodes through `toBlocks_mul_packedShear*` and
`toMatrix_packedLayer*Param` to `shearZ / shearX (layerZParam / layerXParam (toBlocks n a) ε)` times
`toBlocks n a` (on the matching side), and the nonzero parameter transports to the `Matrix` one
via `packedLayerZParam_eq_zero_iff` / `packedLayerXParam_eq_zero_iff` — exactly the data
`IsBlockMove` requires. Size-generic (all `n`, all `a`); the forward direction the next chunk's
`packedReaches → ReachesTerminalIn` consumes. -/
theorem packedNeighbors_sound {n a a' : ℕ} (h : a' ∈ packedNeighbors n a) :
    IsBlockMove (toBlocks n a) (toBlocks n a') := by
  rw [packedNeighbors, List.mem_flatMap] at h
  obtain ⟨ε, -, hmem⟩ := h
  rw [List.mem_append] at hmem
  rcases hmem with hz | hx
  · obtain ⟨hp, rfl | rfl⟩ := mem_guarded_pair hz
    · exact Or.inl ⟨ε, mt (packedLayerZParam_eq_zero_iff n a ε).mpr hp,
        Or.inl (by rw [toBlocks_mul_packedShearZ_left, toMatrix_packedLayerZParam])⟩
    · exact Or.inl ⟨ε, mt (packedLayerZParam_eq_zero_iff n a ε).mpr hp,
        Or.inr (by rw [toBlocks_mul_packedShearZ_right, toMatrix_packedLayerZParam])⟩
  · obtain ⟨hp, rfl | rfl⟩ := mem_guarded_pair hx
    · exact Or.inr ⟨ε, mt (packedLayerXParam_eq_zero_iff n a ε).mpr hp,
        Or.inl (by rw [toBlocks_mul_packedShearX_left, toMatrix_packedLayerXParam])⟩
    · exact Or.inr ⟨ε, mt (packedLayerXParam_eq_zero_iff n a ε).mpr hp,
        Or.inr (by rw [toBlocks_mul_packedShearX_right, toMatrix_packedLayerXParam])⟩

/-! ### Kernel-tractability guards

These `decide` checks exercise the packed neighbour construction natively at the two block widths
the finite verification `lem-local` runs over. A terminal block (the packed Gram matrix
`J = [[0, I], [I, 0]]`) has every parameter zero, so it has no moves — its neighbour list is empty
(a terminal block is a fixed point of the walk); a non-terminal block has a nonzero list. -/

end CliffordCSS.Packed

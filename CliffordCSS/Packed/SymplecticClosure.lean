import CliffordCSS.Packed.BinaryMatrix

/-!
# Packed encoder algebra for the `Sp(2n, 𝔽₂)` closure (Beyond transversality, App. D.1)

Pure mathematics : the algebra of the packed encoder `ofBlocks`
(defined beside its decoder `toBlocks` in `CliffordCSS/Packed/BinaryMatrix.lean`) that the *Local
reduction* completeness closure builds on — its **multiplicativity**, the **packed identity** the
closure is seeded from, and its **faithfulness** to symplectic membership. It names only raw
carriers (`Matrix`, `Nat`, `Fin`, `ZMod 2`) and the this library symplectic group.

## Why this exists (the W4 completeness substrate)

The certificate-route plan for Theorem D.1 (`dec-conditional-d1-certificate-route`, refined by
`dec-d4-kernel-computed-reachability`) discharges the *Local reduction* lemma (`lem-local`,
Lemma D.4) by a **kernel computation** on the packed representation: build the element list of
`Sp(4, 𝔽₂)` (resp. `Sp(2, 𝔽₂)`) by closure from the elementary Clifford generators, then reverse-BFS
that list for reachability. `PackedBinaryMatrix.lean` supplies the packed calculus (`mul`,
`transpose`, `IsPackedSymplectic`) with both the *decoder* `toBlocks` and its inverse *encoder*
`ofBlocks` (`toBlocks_ofBlocks`, `ofBlocks_lt`); this file adds the `ofBlocks` algebra the closure
needs — it turns a `Matrix`-level word in the generators into the packed product of their packings,
seeds the closure from the packed identity, and certifies a packed element assembled from symplectic
generators as symplectic. Work item **W4** of the plan; this is its
foundational chunk.

## What is proved here

* `mul_ofBlocks` — `mul (n + n) (ofBlocks n A) (ofBlocks n B) = ofBlocks n (A * B)`: `ofBlocks`
  carries the `Matrix` product to the packed product `mul`, so a word in the generators packs to the
  packed product of their packings. This is what makes the closure list a *monoid* image.
* `one` / `ofBlocks_one` / `toBlocks_one` / `one_lt` / `one_mul_of_lt` / `mul_one_of_lt` — the
  packed identity `one n` (the packing of `1`), the seed the closure starts from, with its decode
  and its left/right unit laws on the enumeration range.
* `isPackedSymplectic_ofBlocks_iff` — `IsPackedSymplectic n (ofBlocks n G) ↔ G ∈
  binarySymplecticGroup (Fin n)`: the packed symplectic test on `ofBlocks n G` decides genuine
  membership of `G`, so a packed element built from symplectic generators certifies as symplectic.

The encoder `ofBlocks` itself, its section property `toBlocks_ofBlocks`, and the range bound
`ofBlocks_lt` are defined beside the decoder `toBlocks` in `CliffordCSS/Packed/BinaryMatrix.lean`
(colocated as `ofMatrix` is with `toMatrix`), and are imported above.
-/

open Matrix

namespace CliffordCSS.Packed

variable {n : ℕ}

/-- **`ofBlocks` is multiplicative into the packed product**:
`mul (n + n) (ofBlocks n A) (ofBlocks n B) = ofBlocks n (A * B)`. It carries the `Matrix` product to
the packed product `mul`, so packing a `Matrix`-level word in the generators equals the packed
product of the packed generators — the fact that turns the block-diagonal closure into a *monoid*
image of `Sp(2n, 𝔽₂)`. Both sides are in range (`mul_lt`, `ofBlocks_lt`), so it suffices to check
the block decodings agree (`toBlocks_inj_of_lt`): `toBlocks_mul` and `toBlocks_ofBlocks` reduce both
to `A * B`. -/
theorem mul_ofBlocks (n : ℕ) (A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) :
    mul (n + n) (ofBlocks n A) (ofBlocks n B) = ofBlocks n (A * B) := by
  refine toBlocks_inj_of_lt (mul_lt _ _ _) (ofBlocks_lt n (A * B)) ?_
  rw [toBlocks_mul, toBlocks_ofBlocks, toBlocks_ofBlocks, toBlocks_ofBlocks]

/-- **The packed identity** `one n`: the packing of the identity matrix `1`. The seed the
generator closure starts from; characterised by `toBlocks_one` and the left/right unit laws
`one_mul_of_lt` / `mul_one_of_lt`. -/
def one (n : ℕ) : ℕ := ofBlocks n 1

/-- The packed identity is the packing of `1`, `ofBlocks n (1 : Matrix …) = one n` (definitional);
stated as a lemma so the closure development can rewrite `ofBlocks` of the `Matrix` identity to the
canonical seed `one n`. -/
theorem ofBlocks_one (n : ℕ) :
    ofBlocks n (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) = one n := rfl


end CliffordCSS.Packed

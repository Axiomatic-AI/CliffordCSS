import CliffordCSS.DepthOne.Families

/-!
# Automatic parameters (Beyond transversality, App. D.1 — Lemma D.2)

Pure mathematics : **Lemma D.2 (Automatic parameters)** of §D.1 of
*Beyond transversality* (arXiv:2608.05688), the lemma that "manufactures the moves" for the
fixed-matching generation theorem (Theorem D.1). Everything is `𝔽₂` symplectic linear algebra naming
the raw carrier `Matrix`.

## The paper's lemma (§D.1, "Validity and automatically valid diagonal circuits")

> **Lemma D.2 (Automatic parameters).** Let `G ∈ N_M`. Then every matrix in the two spans
> `𝒮₊(G) = span {A Bᵀ, Dᵀ B, B + Bᵀ}`, `𝒮₋(G) = span {C Dᵀ, Cᵀ A, C + Cᵀ}` is symmetric and
> `M`-block-diagonal, and `C_X S ⊆ C_Z` for `S ∈ 𝒮₊(G)`, `C_Z T ⊆ C_X` for `T ∈ 𝒮₋(G)`.
> Consequently `U_Z(S) ∈ S^Z_M` and `L_X(T) ∈ S^X_M` for all such `S` and `T`.

Here `G = [[A, B], [C, D]]` is a code-preserving, `M`-block-diagonal (depth-one `2`-local)
symplectic matrix, i.e. `G ∈ N_M = fixedMatchingSlice`. The three properties "symmetric ∧
`M`-block-diagonal ∧
`C_X S ⊆ C_Z`" are exactly membership in the `Z`-diagonal parameter space `S^Z_M =
admissibleParamsBlockDiag C_X C_Z σ` (and dually `C_Z T ⊆ C_X` gives `S^X_M =
admissibleParamsBlockDiag C_Z C_X σ`), so each span statement is a single submodule inclusion `≤`.

The heart of the lemma is the six *validity* inclusions. The paper reads them off the conjugate
`G Pₓ G⁻¹` of the (singular, non-symplectic) `X`-projector `Pₓ = [[I, 0], [0, 0]]`, working inside
the associative algebra `End_𝓛` of `𝒞`-preserving linear maps — the one place the argument steps
outside the group. We reach the identical six inclusions directly from validity (Eq. (d1-valid),
`mem_codePreservingGroup_fromBlocks_iff`) applied to `G` *and* to `G⁻¹ = [[Dᵀ, Bᵀ], [Cᵀ, Aᵀ]]`
(Eq. (d1-inv), `coe_inv_eq_fromBlocks`), which is a faithful and shorter route to the same
conclusion: e.g. `C_X (A Bᵀ) ⊆ C_Z` because `C_X A ⊆ C_X` (validity of `G`) then `C_X Bᵀ ⊆ C_Z`
(validity of `G⁻¹`), using `x ᵥ* (A * Bᵀ) = (x ᵥ* A) ᵥ* Bᵀ`. Symmetry is read off the symplectic
block relations (Eq. (d1-sympl), `fromBlocks_symplectic_relations`); `M`-block-diagonality from the
block-diagonality of `A, B, C, D` (`isSpBlockDiagonal_fromBlocks_iff`) via the closure of
`IsCellDiagonal` under sum, product and transpose.

No orthogonality `C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more".

## What is proved

* `automaticParamsZ_le` — Lemma D.2, upper span: for `G ∈ N_M` with `G = [[A, B], [C, D]]`,
  `span {A Bᵀ, Dᵀ B, B + Bᵀ} ≤ S^Z_M` (the parameter space `admissibleParamsBlockDiag C_X C_Z σ`).
* `automaticParamsX_le` — Lemma D.2, lower span: `span {C Dᵀ, Cᵀ A, C + Cᵀ} ≤ S^X_M`
  (`admissibleParamsBlockDiag C_Z C_X σ`).
* `shearZ_mem_shearZFamilyM` / `shearX_mem_shearXFamilyM` — the "consequently `U_Z(S) ∈ S^Z_M`,
  `L_X(T) ∈ S^X_M`" corollary: any admissible, `M`-block-diagonal parameter's diagonal circuit lies
  in the `M`-block-diagonal family. Composing with the span inclusions turns each manufactured
  parameter into an element of the generating family `S^Z_M` / `S^X_M`.
* `automaticShearZ_mem_shearZFamilyM` / `automaticShearX_mem_shearXFamilyM` — Lemma D.2's closing
  "Consequently … for all such `S` and `T`", composed over the whole span: for `G ∈ N_M`, *every*
  `S ∈ 𝒮₊(G)` (resp. `T ∈ 𝒮₋(G)`) has `U_Z(S) ∈ S^Z_M` (resp. `L_X(T) ∈ S^X_M`). Each is the
  span-inclusion composed with the single-parameter consequence.
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Lemma D.2 (Automatic parameters): the two spans lie in `S^Z_M`, `S^X_M`

The closure of the entrywise `M`-block-diagonal predicate `IsCellDiagonal σ` under sum, product and
transpose — `isCellDiagonal_add` / `isCellDiagonal_mul` / `isCellDiagonal_transpose`, used below for
the block-diagonality half of the lemma — lives upstream in `BeyondTransversalityBlockDiagonal`
(alongside the identity/zero cases and the inverse closure). -/

/-- **Lemma D.2, upper span `𝒮₊(G)`.** For a code-preserving, `M`-block-diagonal symplectic matrix
`G ∈ N_M` with blocks `G = [[A, B], [C, D]]`, the span of the three manufactured `Z`-parameters
`A Bᵀ`, `Dᵀ B`, `B + Bᵀ` is contained in the `Z`-diagonal parameter space `S^Z_M =
admissibleParamsBlockDiag C_X C_Z σ`: every element is symmetric, `M`-block-diagonal, and satisfies
`C_X S ⊆ C_Z`.

Symmetry comes from the symplectic block relations (`A Bᵀ = B Aᵀ`, `Bᵀ D = Dᵀ B`); validity from
`C_X A ⊆ C_X`, `C_X B ⊆ C_Z` (validity of `G`) and `C_X Dᵀ ⊆ C_X`, `C_X Bᵀ ⊆ C_Z` (validity of
`G⁻¹ = [[Dᵀ, Bᵀ], [Cᵀ, Aᵀ]]`); block-diagonality from that of `A, B, D` and the closure of
`IsCellDiagonal`. -/
theorem automaticParamsZ_le {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)} {σ : Equiv.Perm ι}
    {hσ : Function.Involutive σ} {G : ↥(binarySymplecticGroup ι)} {A B C D : Matrix ι ι (ZMod 2)}
    (hG : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = Matrix.fromBlocks A B C D)
    (hGN : G ∈ fixedMatchingSlice C_X C_Z σ hσ) :
    Submodule.span (ZMod 2) {A * Bᵀ, Dᵀ * B, B + Bᵀ} ≤ admissibleParamsBlockDiag C_X C_Z σ := by
  obtain ⟨hN, hMbd⟩ := mem_fixedMatchingSlice_iff.mp hGN
  obtain ⟨hAv, hBv, _, _⟩ := (mem_codePreservingGroup_fromBlocks_iff hG).mp hN
  obtain ⟨hDtv, hBtv, _, _⟩ :=
    (mem_codePreservingGroup_fromBlocks_iff (coe_inv_eq_fromBlocks hG)).mp (inv_mem hN)
  rw [hG, isSpBlockDiagonal_fromBlocks_iff] at hMbd
  obtain ⟨hAd, hBd, _, hDd⟩ := hMbd
  have hGsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι := hG ▸ G.2
  obtain ⟨hABs, _, _, hBtD, _, _⟩ := fromBlocks_symplectic_relations hGsymp
  refine Submodule.span_le.mpr ?_
  rintro S (rfl | rfl | rfl)
  · refine mem_admissibleParamsBlockDiag.mpr ⟨?_, fun x hx => ?_, ?_⟩
    · change (A * Bᵀ)ᵀ = A * Bᵀ
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]; exact hABs.symm
    · rw [← Matrix.vecMul_vecMul]; exact hBtv _ (hAv x hx)
    · exact isCellDiagonal_mul hσ hAd (isCellDiagonal_transpose hσ hBd)
  · refine mem_admissibleParamsBlockDiag.mpr ⟨?_, fun x hx => ?_, ?_⟩
    · change (Dᵀ * B)ᵀ = Dᵀ * B
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]; exact hBtD
    · rw [← Matrix.vecMul_vecMul]; exact hBv _ (hDtv x hx)
    · exact isCellDiagonal_mul hσ (isCellDiagonal_transpose hσ hDd) hBd
  · refine mem_admissibleParamsBlockDiag.mpr
      ⟨Matrix.isSymm_add_transpose_self B, fun x hx => ?_, ?_⟩
    · rw [Matrix.vecMul_add]; exact C_Z.add_mem (hBv x hx) (hBtv x hx)
    · exact isCellDiagonal_add hBd (isCellDiagonal_transpose hσ hBd)

/-- **Lemma D.2, lower span `𝒮₋(G)`.** Dual to `automaticParamsZ_le` under the `X ↔ Z` swap: for
`G ∈ N_M` with `G = [[A, B], [C, D]]`, the span of the three manufactured `X`-parameters `C Dᵀ`,
`Cᵀ A`, `C + Cᵀ` is contained in the `X`-diagonal parameter space `S^X_M =
admissibleParamsBlockDiag C_Z C_X σ`: every element is symmetric, `M`-block-diagonal, and satisfies
`C_Z T ⊆ C_X`. -/
theorem automaticParamsX_le {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)} {σ : Equiv.Perm ι}
    {hσ : Function.Involutive σ} {G : ↥(binarySymplecticGroup ι)} {A B C D : Matrix ι ι (ZMod 2)}
    (hG : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = Matrix.fromBlocks A B C D)
    (hGN : G ∈ fixedMatchingSlice C_X C_Z σ hσ) :
    Submodule.span (ZMod 2) {C * Dᵀ, Cᵀ * A, C + Cᵀ} ≤ admissibleParamsBlockDiag C_Z C_X σ := by
  obtain ⟨hN, hMbd⟩ := mem_fixedMatchingSlice_iff.mp hGN
  obtain ⟨hAv, _, hCv, _⟩ := (mem_codePreservingGroup_fromBlocks_iff hG).mp hN
  obtain ⟨hDtv, _, hCtv, _⟩ :=
    (mem_codePreservingGroup_fromBlocks_iff (coe_inv_eq_fromBlocks hG)).mp (inv_mem hN)
  rw [hG, isSpBlockDiagonal_fromBlocks_iff] at hMbd
  obtain ⟨hAd, _, hCd, hDd⟩ := hMbd
  have hGsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι := hG ▸ G.2
  obtain ⟨_, hCDs, hAtC, _, _, _⟩ := fromBlocks_symplectic_relations hGsymp
  refine Submodule.span_le.mpr ?_
  rintro S (rfl | rfl | rfl)
  · refine mem_admissibleParamsBlockDiag.mpr ⟨?_, fun z hz => ?_, ?_⟩
    · change (C * Dᵀ)ᵀ = C * Dᵀ
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]; exact hCDs.symm
    · rw [← Matrix.vecMul_vecMul]; exact hDtv _ (hCv z hz)
    · exact isCellDiagonal_mul hσ hCd (isCellDiagonal_transpose hσ hDd)
  · refine mem_admissibleParamsBlockDiag.mpr ⟨?_, fun z hz => ?_, ?_⟩
    · change (Cᵀ * A)ᵀ = Cᵀ * A
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]; exact hAtC
    · rw [← Matrix.vecMul_vecMul]; exact hAv _ (hCtv z hz)
    · exact isCellDiagonal_mul hσ (isCellDiagonal_transpose hσ hCd) hAd
  · refine mem_admissibleParamsBlockDiag.mpr
      ⟨Matrix.isSymm_add_transpose_self C, fun z hz => ?_, ?_⟩
    · rw [Matrix.vecMul_add]; exact C_X.add_mem (hCv z hz) (hCtv z hz)
    · exact isCellDiagonal_add hCd (isCellDiagonal_transpose hσ hCd)

/-! ### The consequence: manufactured diagonal circuits lie in `S^Z_M`, `S^X_M` -/

/-- **Lemma D.2, consequence (`Z`).** For any admissible, `M`-block-diagonal parameter
`S ∈ S^Z_M = admissibleParamsBlockDiag C_X C_Z σ`, the `Z`-diagonal circuit
`U_Z(S) = [[I, S], [0, I]]` lies in the `M`-block-diagonal `Z`-diagonal family `S^Z_M =
shearZFamilyM`. Combined with
`automaticParamsZ_le`, every parameter in `𝒮₊(G)` yields an element `U_Z(S) ∈ S^Z_M`. -/
theorem shearZ_mem_shearZFamilyM {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)} {σ : Equiv.Perm ι}
    (hσ : Function.Involutive σ) {S : Matrix ι ι (ZMod 2)}
    (hS : S ∈ admissibleParamsBlockDiag C_X C_Z σ) {G : ↥(binarySymplecticGroup ι)}
    (hGS : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = shearZ S) :
    G ∈ shearZFamilyM C_X C_Z σ hσ := by
  obtain ⟨hSsymm, hSvalid, hScell⟩ := mem_admissibleParamsBlockDiag.mp hS
  rw [mem_shearZFamilyM]
  refine ⟨⟨S, mem_admissibleParams.mpr ⟨hSsymm, hSvalid⟩, hGS⟩, ?_⟩
  rw [hGS, shearZ, isSpBlockDiagonal_fromBlocks_iff]
  exact ⟨isCellDiagonal_one σ, hScell, isCellDiagonal_zero σ, isCellDiagonal_one σ⟩

/-- **Lemma D.2, consequence (`X`).** Dual to `shearZ_mem_shearZFamilyM`: for any admissible,
`M`-block-diagonal parameter `T ∈ S^X_M = admissibleParamsBlockDiag C_Z C_X σ`, the `X`-diagonal
circuit `L_X(T) = [[I, 0], [T, I]]` lies in the `M`-block-diagonal `X`-diagonal family
`S^X_M = shearXFamilyM`. -/
theorem shearX_mem_shearXFamilyM {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)} {σ : Equiv.Perm ι}
    (hσ : Function.Involutive σ) {T : Matrix ι ι (ZMod 2)}
    (hT : T ∈ admissibleParamsBlockDiag C_Z C_X σ) {G : ↥(binarySymplecticGroup ι)}
    (hGT : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = shearX T) :
    G ∈ shearXFamilyM C_X C_Z σ hσ := by
  obtain ⟨hTsymm, hTvalid, hTcell⟩ := mem_admissibleParamsBlockDiag.mp hT
  rw [mem_shearXFamilyM]
  refine ⟨⟨T, mem_admissibleParams.mpr ⟨hTsymm, hTvalid⟩, hGT⟩, ?_⟩
  rw [hGT, shearX, isSpBlockDiagonal_fromBlocks_iff]
  exact ⟨isCellDiagonal_one σ, isCellDiagonal_zero σ, hTcell, isCellDiagonal_one σ⟩

/-! ### Lemma D.2, the "Consequently …" conclusion, composed over the whole span

The paper closes Lemma D.2 with "Consequently `U_Z(S) ∈ E^↑_M` and `L_X(T) ∈ E^↓_M` for all such
`S` and `T`". The two theorems below state exactly that composed conclusion: quantified over *every*
parameter in the manufactured span `𝒮₊(G)` / `𝒮₋(G)`, the corresponding diagonal circuit lands in
the generating family `S^Z_M` / `S^X_M`. Each is the span-inclusion (`automaticParamsZ_le` /
`automaticParamsX_le`) composed with the single-parameter consequence (`shearZ_mem_shearZFamilyM` /
`shearX_mem_shearXFamilyM`). -/


end CliffordCSS

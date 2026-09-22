import CliffordCSS.DepthOne.LocalMove

/-!
# Cell blocks of a layer (Beyond transversality, App. D.1 — the D.5 bridge)

Pure mathematics : the bridge between a **global layer** `G` and its
**cell blocks** `g_𝔟`, for the *reduction by multiplication* proof of Theorem D.1 of *Beyond
transversality* (arXiv:2608.05688). Everything is `𝔽₂` symplectic linear algebra.

For a cell `𝔟` (a `σ`-closed finset of qubits, `cellFinset σ i = {i, σ i}`), `localBlock 𝔟 G` is the
block `g_𝔟 = [[A_𝔟, B_𝔟], [C_𝔟, D_𝔟]] ∈ Sp(2 w_𝔟, 𝔽₂)` of Eq. (d1-gb) — the four blocks of `G`
restricted to the cell. What the global reduction (Lemma D.6) needs of it is exactly four things,
each proved here:

* **it is a block**: `localBlock_mem_binarySymplecticGroup` — the cell block of an
  `M`-block-diagonal symplectic layer is symplectic, so the local reduction of Lemma D.4 applies;
* **restriction is multiplicative on layers**: `localBlock_mul` — `(G H)_𝔟 = G_𝔟 H_𝔟` whenever the
  **left** factor is `M`-block-diagonal (the same one-sided crux as
  `restrictToCell_mul_of_cellDiagonal`), together with `localBlock_shearZ` / `localBlock_shearX`
  (`U_Z(S)_𝔟 = U_Z(S_𝔟)`). Multiplying the layer by a manufactured diagonal circuit therefore acts
  on each cell block by the corresponding local diagonal circuit;
* **the parameters restrict** (Lemma D.5, in the packaging used downstream):
  `layerZParam_localBlock` / `layerXParam_localBlock` — `S^Z(G, ε)_𝔟 = S^Z(g_𝔟, ε)`, so one global
  choice of `ε` induces the intended local move at the working cell;
* **blockwise terminality assembles**: `isTerminalLayer_of_forall_cell` — a layer all of whose cell
  blocks are terminal is terminal, via `eq_zero_of_forall_restrictToCell_eq_zero`
  (`BeyondTransversalityRestrict`: an `M`-block-diagonal matrix vanishing on every cell vanishes).

The cell-independent ingredients live in the files that own their vocabulary and are only *used*
here: `restrictToCell_one`, `eq_zero_of_forall_restrictToCell_eq_zero` and `spzParam_mem_span` /
`spxParam_mem_span` in `BeyondTransversalityRestrict`, and
`spzParam_eq_zero_of_isTerminalBlock` / `spxParam_eq_zero_of_isTerminalBlock` (terminality is
absorbing: every parameter available at a terminal block is `0`, so a later move restricts to the
identity there) in `BeyondTransversalityLocalMove`, the lowest file naming both `spzParam` and
`IsTerminalBlock`.

No orthogonality `C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more".
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The cell block of a layer -/

/-- **The cell block `g_𝔟` of a layer `G` (Eq. (d1-gb))**: the four blocks of `G` restricted to the
cell `𝔟`, reassembled as a matrix on `𝔟 ⊕ 𝔟`. For a cell `𝔟 = {i, σ i}` this is the paper's
`g_𝔟 = [[A_𝔟, B_𝔟], [C_𝔟, D_𝔟]] ∈ Sp(2 w_𝔟, 𝔽₂)` with `w_𝔟 = #𝔟 ∈ {1, 2}`. -/
def localBlock (b : Finset ι) (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) :
    Matrix (b ⊕ b) (b ⊕ b) (ZMod 2) :=
  Matrix.fromBlocks (restrictToCell b G.toBlocks₁₁) (restrictToCell b G.toBlocks₁₂)
    (restrictToCell b G.toBlocks₂₁) (restrictToCell b G.toBlocks₂₂)

omit [Fintype ι] [DecidableEq ι] in
/-- The cell block of a layer presented in block form is the block form of the restricted blocks. -/
@[simp] theorem localBlock_fromBlocks (b : Finset ι) (A B C D : Matrix ι ι (ZMod 2)) :
    localBlock b (Matrix.fromBlocks A B C D)
      = Matrix.fromBlocks (restrictToCell b A) (restrictToCell b B)
          (restrictToCell b C) (restrictToCell b D) := rfl

omit [Fintype ι] in
/-- The cell block of a `Z`-diagonal circuit is the `Z`-diagonal circuit of the restricted
parameter: `U_Z(S)_𝔟 = U_Z(S_𝔟)`. -/
@[simp] theorem localBlock_shearZ (b : Finset ι) (S : Matrix ι ι (ZMod 2)) :
    localBlock b (shearZ S) = shearZ (restrictToCell b S) := by
  rw [shearZ, localBlock_fromBlocks, restrictToCell_one, restrictToCell_zero, shearZ]

omit [Fintype ι] in
/-- The cell block of an `X`-diagonal circuit is the `X`-diagonal circuit of the restricted
parameter: `L_X(T)_𝔟 = L_X(T_𝔟)`. -/
@[simp] theorem localBlock_shearX (b : Finset ι) (T : Matrix ι ι (ZMod 2)) :
    localBlock b (shearX T) = shearX (restrictToCell b T) := by
  rw [shearX, localBlock_fromBlocks, restrictToCell_one, restrictToCell_zero, shearX]

omit [DecidableEq ι] in
/-- **Restriction to a cell is multiplicative on layers**: `(G H)_𝔟 = G_𝔟 H_𝔟` for a `σ`-closed cell
`𝔟`, as soon as the **left** factor `G` is `M`-block-diagonal (`IsSpBlockDiagonal σ`); `H` is
arbitrary. Each of the eight products in `Matrix.fromBlocks_multiply` has an `M`-block-diagonal left
factor, so `restrictToCell_mul_of_cellDiagonal` applies to it, and restriction is additive. This is
why multiplying a layer by a manufactured, `M`-supported diagonal circuit acts on every cell block
separately, `(U_Z(S) G)|_𝔟 = U_Z(S_𝔟) g_𝔟`. -/
theorem localBlock_mul {σ : Equiv.Perm ι} {b : Finset ι} (hb : ∀ a ∈ b, σ a ∈ b)
    {G H : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} (hG : IsSpBlockDiagonal σ G) :
    localBlock b (G * H) = localBlock b G * localBlock b H := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, G = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks G).symm⟩
  obtain ⟨P, Q, R, S, rfl⟩ : ∃ P Q R S, H = Matrix.fromBlocks P Q R S :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks H).symm⟩
  obtain ⟨hA, hB, hC, hD⟩ := (isSpBlockDiagonal_fromBlocks_iff A B C D).mp hG
  rw [Matrix.fromBlocks_multiply, localBlock_fromBlocks, localBlock_fromBlocks,
    localBlock_fromBlocks, Matrix.fromBlocks_multiply]
  simp only [restrictToCell_add, restrictToCell_mul_of_cellDiagonal hb hA,
    restrictToCell_mul_of_cellDiagonal hb hB, restrictToCell_mul_of_cellDiagonal hb hC,
    restrictToCell_mul_of_cellDiagonal hb hD]

/-- **The cell block of a layer is a block**: for a `σ`-closed cell `𝔟`, the cell block of an
`M`-block-diagonal symplectic layer `G` lies in `Sp(2 w_𝔟, 𝔽₂)`. Each of the three block relations
of `fromBlocks_mem_binarySymplecticGroup_iff` — `A Bᵀ = B Aᵀ`, `C Dᵀ = D Cᵀ`, `A Dᵀ + B Cᵀ = I` —
restricts to the cell, since restriction commutes with transposition and addition, is multiplicative
on `M`-block-diagonal left factors, and fixes the identity. This is what lets the local reduction of
Lemma D.4, a statement about `Sp(2)` and `Sp(4)`, be applied to `g_𝔟`. -/
theorem localBlock_mem_binarySymplecticGroup {σ : Equiv.Perm ι}
    {b : Finset ι} (hb : ∀ a ∈ b, σ a ∈ b) {G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)}
    (hGsymp : G ∈ binarySymplecticGroup ι) (hG : IsSpBlockDiagonal σ G) :
    localBlock b G ∈ binarySymplecticGroup b := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, G = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks G).symm⟩
  obtain ⟨hA, hB, hC, hD⟩ := (isSpBlockDiagonal_fromBlocks_iff A B C D).mp hG
  obtain ⟨h1, h2, h3⟩ := (fromBlocks_mem_binarySymplecticGroup_iff A B C D).mp hGsymp
  have hres : ∀ (X Y : Matrix ι ι (ZMod 2)), IsCellDiagonal σ X →
      restrictToCell b (X * Yᵀ) = restrictToCell b X * (restrictToCell b Y)ᵀ := by
    intro X Y hX
    rw [restrictToCell_mul_of_cellDiagonal hb hX, restrictToCell_transpose]
  rw [localBlock_fromBlocks, fromBlocks_mem_binarySymplecticGroup_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hres A B hA, ← hres B A hB, h1]
  · rw [← hres C D hC, ← hres D C hD, h2]
  · rw [← hres A D hA, ← hres B C hB, ← restrictToCell_add, h3, restrictToCell_one]

/-! ### Lemma D.5 in the packaging used by the global reduction -/

omit [DecidableEq ι] in
/-- **Lemma D.5, `Z` side, for cell blocks**: the `Z`-parameter of the cell block is the restriction
of the global `Z`-parameter at the *same* coefficient vector, `S^Z(g_𝔟, ε) = S^Z(G, ε)_𝔟`. Hence a
move chosen at the working cell is induced by re-evaluating the same `ε` on the whole layer. -/
theorem layerZParam_localBlock {σ : Equiv.Perm ι} (hσ : Function.Involutive σ) {b : Finset ι}
    (hb : ∀ a ∈ b, σ a ∈ b) {G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} (hG : IsSpBlockDiagonal σ G)
    (ε : Fin 3 → ZMod 2) :
    layerZParam (localBlock b G) ε = restrictToCell b (layerZParam G ε) := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, G = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks G).symm⟩
  obtain ⟨hA, _, _, hD⟩ := (isSpBlockDiagonal_fromBlocks_iff A B C D).mp hG
  rw [localBlock_fromBlocks, layerZParam_fromBlocks, layerZParam_fromBlocks,
    restrictToCell_spzParam hσ hb hA hD]

omit [DecidableEq ι] in
/-- **Lemma D.5, `X` side, for cell blocks** (dual to `layerZParam_localBlock`):
`S^X(g_𝔟, ε) = S^X(G, ε)_𝔟`. -/
theorem layerXParam_localBlock {σ : Equiv.Perm ι} (hσ : Function.Involutive σ) {b : Finset ι}
    (hb : ∀ a ∈ b, σ a ∈ b) {G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} (hG : IsSpBlockDiagonal σ G)
    (ε : Fin 3 → ZMod 2) :
    layerXParam (localBlock b G) ε = restrictToCell b (layerXParam G ε) := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, G = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks G).symm⟩
  obtain ⟨_, _, hC, _⟩ := (isSpBlockDiagonal_fromBlocks_iff A B C D).mp hG
  rw [localBlock_fromBlocks, layerXParam_fromBlocks, layerXParam_fromBlocks,
    restrictToCell_spxParam hσ hb hC]

/-! ### Blockwise terminality assembles -/

/-- **A layer all of whose cell blocks are terminal is terminal.** Each of the six generators of
Eq. (d1-term) is an `M`-block-diagonal matrix (products, transposes and sums of the
`M`-block-diagonal blocks of `G`) whose restriction to every cell is the corresponding generator of
that cell block, hence `0`; so each generator vanishes globally
(`eq_zero_of_forall_restrictToCell_eq_zero`). This is the step that turns the blockwise-terminal
output of the global reduction (Lemma D.6) into the hypothesis of the terminal factorization
(Eq. (d1-factor)). -/
theorem isTerminalLayer_of_forall_cell {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    {G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} (hG : IsSpBlockDiagonal σ G)
    (h : ∀ i, IsTerminalLayer (localBlock (cellFinset σ i) G)) : IsTerminalLayer G := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, G = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks G).symm⟩
  obtain ⟨hA, hB, hC, hD⟩ := (isSpBlockDiagonal_fromBlocks_iff A B C D).mp hG
  simp only [localBlock_fromBlocks, isTerminalLayer_fromBlocks, IsTerminalBlock] at h
  have hcell := fun i => cellFinset_sigma_closed hσ i
  change IsTerminalBlock A B C D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_zero_of_forall_restrictToCell_eq_zero
      (isCellDiagonal_mul hσ hA (isCellDiagonal_transpose hσ hB)) fun i => ?_
    rw [restrictToCell_mul_of_cellDiagonal (hcell i) hA, restrictToCell_transpose]
    exact (h i).1
  · refine eq_zero_of_forall_restrictToCell_eq_zero
      (isCellDiagonal_mul hσ (isCellDiagonal_transpose hσ hD) hB) fun i => ?_
    rw [restrictToCell_mul_of_cellDiagonal (hcell i) (isCellDiagonal_transpose hσ hD),
      restrictToCell_transpose]
    exact (h i).2.1
  · refine eq_zero_of_forall_restrictToCell_eq_zero
      (isCellDiagonal_add hB (isCellDiagonal_transpose hσ hB)) fun i => ?_
    rw [restrictToCell_add, restrictToCell_transpose]
    exact (h i).2.2.1
  · refine eq_zero_of_forall_restrictToCell_eq_zero
      (isCellDiagonal_mul hσ hC (isCellDiagonal_transpose hσ hD)) fun i => ?_
    rw [restrictToCell_mul_of_cellDiagonal (hcell i) hC, restrictToCell_transpose]
    exact (h i).2.2.2.1
  · refine eq_zero_of_forall_restrictToCell_eq_zero
      (isCellDiagonal_mul hσ (isCellDiagonal_transpose hσ hC) hA) fun i => ?_
    rw [restrictToCell_mul_of_cellDiagonal (hcell i) (isCellDiagonal_transpose hσ hC),
      restrictToCell_transpose]
    exact (h i).2.2.2.2.1
  · refine eq_zero_of_forall_restrictToCell_eq_zero
      (isCellDiagonal_add hC (isCellDiagonal_transpose hσ hC)) fun i => ?_
    rw [restrictToCell_add, restrictToCell_transpose]
    exact (h i).2.2.2.2.2

end CliffordCSS

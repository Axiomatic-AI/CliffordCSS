import CliffordCSS.DepthOne.Word
import CliffordCSS.DepthOne.Terminal

/-!
# Terminal layers factor (Beyond transversality, App. D.1 — Eq. (d1-factor))

Pure mathematics : the **terminal factorization** of the *reduction
by multiplication* proof of the fixed-matching generation theorem (Theorem D.1, `thm-depthone`) of
*Beyond transversality* (arXiv:2608.05688). Everything is `𝔽₂` symplectic linear algebra naming the
raw carrier `Matrix`.

## What a terminal layer is, and why it factors

The reverse inclusion `N_M ⊆ ⟨S^Z_M, S^X_M, L_M⟩` of Theorem D.1 reduces an arbitrary `G ∈ N_M` — by
left/right multiplication with valid diagonal circuits — to a **blockwise-terminal** layer
`G_term = [[A, B], [C, D]]`, one on which all six automatic parameters of Lemma D.2 vanish
(`IsTerminalBlock A B C D`, Eq. (d1-term)). The paper (§D.1, "Terminal layers factor") then exhibits
`G_term` as a product of four valid depth-one layers,
```
  G_term = L* · U_Z(B) · L_X(C) · U_Z(B), (Eq. (d1-factor))
```
with `L* ∈ L_M` a Levi gate and `U_Z(B) ∈ S^Z_M`, `L_X(C) ∈ S^X_M` the two diagonal circuits, so
`G_term` already lies in the generated group. That is the content delivered here.

## The direct global proof (bypassing the per-cell rank classification)

The paper reaches Eq. (d1-factor) through Lemma D.7 (Terminal normal form), a *per-cell* rank case
analysis (width one: `g = Id` or `g = U_Z(1) L_X(1) U_Z(1)`; width two: three rank cases splicing
the local blocks). The assembly then patches the cells together. We instead prove the factorization
**directly and globally**, with no rank argument and no width restriction, from terminality plus the
symplectic relations Eq. (d1-sympl). The two facts that make this work are

* `B C B = B` — right-multiply `A Dᵀ + B C = I` (Eq. (d1-sympl), with `C = Cᵀ`) by `B` and use the
  terminal condition `Dᵀ B = 0`: `(A Dᵀ) B + B C B = B`, and `(A Dᵀ) B = A (Dᵀ B) = 0`;
* `C B C = C` — dually, left-multiply by `C` and use `Cᵀ A = 0` (hence `C A = 0`).

With these, the product `G_term · W` of `G_term = [[A, B], [C, D]]` with the assembly word
`W = U_Z(B) L_X(C) U_Z(B) = [[I + B C, B C B], [C, I + C B]]` (Eq. (d1-W), `word_eq_fromBlocks`)
collapses to the Levi block form
```
  G_term · W = [[A + B C, 0], [0, D + C B]] (terminalBlock_mul_word)
```
— its off-diagonal blocks vanish because `A B = 0`, `D C = 0` (terminal, using `B = Bᵀ`, `C = Cᵀ`)
together with `B C B = B`, `C B C = C`. Since `W` is an involution (`word_mul_self`), rearranging
gives Eq. (d1-factor), `terminalBlock_factor`. No orthogonality `C_X ⊥ C_Z` is used — "a statement
about split subspaces and nothing more".

## From the factorization to group membership

`terminalLayer_mem_sup_familyM` packages the consequence used by the reverse inclusion: a
blockwise-terminal `G ∈ N_M` lies in `⟨S^Z_M, S^X_M, L_M⟩ = S^Z_M ⊔ S^X_M ⊔ L_M`. Writing
`L* := G · W`, the word `W ∈ S^Z_M ⊔ S^X_M` (`word_mem_sup_shearFamilyM`, whose hypotheses —
`B`, `C` symmetric, `M`-block-diagonal, valid — are exactly terminality plus the validity and
block-diagonality of `G ∈ N_M`), while `L* = [[A + B C, 0], [0, D + C B]]` is a Levi gate
(the symplectic relations of the group element `L*` make `A + B C` a unit with inverse-transpose
`D + C B`), code-preserving and `M`-block-diagonal, hence `L* ∈ L_M`. Then `G = L* · W`
(`W² = I`) exhibits `G` in the join.

## What is proved

* `terminalBlock_mul_word` — for a symplectic terminal block,
  `G_term · W = [[A + BC, 0], [0, D + CB]]`.
* `terminalBlock_factor` — Eq. (d1-factor): `G_term = [[A + BC, 0], [0, D + CB]] · W`.
* `terminalLayer_mem_sup_familyM` — a blockwise-terminal `G ∈ N_M` lies in `S^Z_M ⊔ S^X_M ⊔ L_M`
  (the reverse inclusion of Theorem D.1, restricted to terminal layers).
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The terminal factorization identity (Eq. (d1-W)/(d1-factor)) -/

/-- **`G_term · W` is a Levi block.** For a symplectic block matrix `G = [[A, B], [C, D]] ∈
Sp(2n, 𝔽₂)` that is *terminal* (`IsTerminalBlock A B C D`, Eq. (d1-term)), its product with the
assembly word `W = U_Z(B) L_X(C) U_Z(B) = [[I + B C, B C B], [C, I + C B]]` collapses to the Levi
block form `[[A + B C, 0], [0, D + C B]]`.

The proof is a direct global computation, needing neither the paper's per-cell rank classification
(Lemma D.7) nor any width restriction. From terminality, `B` and `C` are symmetric, so `A B = 0`,
`D C = 0`; and the symplectic relation `A Dᵀ + B C = I` (Eq. (d1-sympl)) gives `B C B = B` (right
multiply by `B`, kill `A Dᵀ B = A (Dᵀ B) = 0`) and `C B C = C` (left multiply by `C`, kill
`C A Dᵀ = (C A) Dᵀ = 0`). The four blocks of `G · W` then reduce: the off-diagonal blocks
`A (B C B) + B (I + C B) = B + B = 0` and `C (I + B C) + D C = C + C = 0` vanish over `𝔽₂`, and the
diagonal blocks are `A + B C`, `D + C B`. -/
theorem terminalBlock_mul_word {A B C D : Matrix ι ι (ZMod 2)}
    (hsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι)
    (hterm : IsTerminalBlock A B C D) :
    Matrix.fromBlocks A B C D * word B C
      = Matrix.fromBlocks (A + B * C) 0 0 (D + C * B) := by
  have hBsymm : Bᵀ = B := hterm.isSymm_B
  have hCsymm : Cᵀ = C := hterm.isSymm_C
  obtain ⟨hABt, hDtB, _, hCDt, hCtA, _⟩ := hterm
  have hBB : B + B = 0 := Matrix.add_self_eq_zero B
  have hCC : C + C = 0 := Matrix.add_self_eq_zero C
  have hAB : A * B = 0 := by rw [← hBsymm]; exact hABt
  have hCA : C * A = 0 := by rw [← hCsymm]; exact hCtA
  have hDC : D * C = 0 := by
    have h := congrArg Matrix.transpose hCDt
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero, hCsymm] at h
    exact h
  obtain ⟨_, _, _, _, h5, _⟩ := fromBlocks_symplectic_relations hsymp
  have h5' : A * Dᵀ + B * C = 1 := by rw [← hCsymm]; exact h5
  have hBCB : B * C * B = B := by
    have h : (A * Dᵀ + B * C) * B = 1 * B := by rw [h5']
    rw [add_mul, Matrix.mul_assoc A Dᵀ B, hDtB, Matrix.mul_zero, zero_add, Matrix.one_mul] at h
    exact h
  have hCBC : C * B * C = C := by
    have h : C * (A * Dᵀ + B * C) = C * 1 := by rw [h5']
    rw [mul_add, Matrix.mul_one, ← Matrix.mul_assoc C A Dᵀ, hCA, Matrix.zero_mul, zero_add,
      ← Matrix.mul_assoc C B C] at h
    exact h
  have hABCB : A * (B * C * B) = 0 := by rw [hBCB]; exact hAB
  have e11 : A * (1 + B * C) + B * C = A + B * C := by
    rw [mul_add, Matrix.mul_one, ← Matrix.mul_assoc A B C, hAB, Matrix.zero_mul, add_zero]
  have e12 : A * (B * C * B) + B * (1 + C * B) = 0 := by
    rw [hABCB, zero_add, mul_add, Matrix.mul_one, ← Matrix.mul_assoc B C B, hBCB]
    exact hBB
  have e21 : C * (1 + B * C) + D * C = 0 := by
    rw [mul_add, Matrix.mul_one, ← Matrix.mul_assoc C B C, hCBC, hDC, add_zero]
    exact hCC
  have e22 : C * (B * C * B) + D * (1 + C * B) = D + C * B := by
    rw [hBCB, mul_add, Matrix.mul_one, ← Matrix.mul_assoc D C B, hDC, Matrix.zero_mul, add_zero,
      add_comm]
  rw [word_eq_fromBlocks, Matrix.fromBlocks_multiply, e11, e12, e21, e22]

/-- **Eq. (d1-factor): terminal layers factor.** For a symplectic terminal block
`G = [[A, B], [C, D]]`, `G = [[A + B C, 0], [0, D + C B]] · W` with `W = U_Z(B) L_X(C) U_Z(B)` the
assembly word. Immediate from `terminalBlock_mul_word` and the involution `W W = I`
(`word_mul_self`): `G = G (W W) = (G W) W`. -/
theorem terminalBlock_factor {A B C D : Matrix ι ι (ZMod 2)}
    (hsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι)
    (hterm : IsTerminalBlock A B C D) :
    Matrix.fromBlocks A B C D
      = Matrix.fromBlocks (A + B * C) 0 0 (D + C * B) * word B C := by
  calc Matrix.fromBlocks A B C D
      = Matrix.fromBlocks A B C D * (word B C * word B C) := by
        rw [word_mul_self, Matrix.mul_one]
    _ = Matrix.fromBlocks A B C D * word B C * word B C := by rw [Matrix.mul_assoc]
    _ = Matrix.fromBlocks (A + B * C) 0 0 (D + C * B) * word B C := by
        rw [terminalBlock_mul_word hsymp hterm]

/-! ### Terminal layers lie in the generated group (reverse inclusion, terminal case) -/

/-- **A blockwise-terminal layer of `N_M` lies in `⟨S^Z_M, S^X_M, L_M⟩`.** Let `G ∈ N_M` be a
two-fold transversal-slice element whose block form `[[A, B], [C, D]]` is terminal
(`IsTerminalBlock`, i.e. every cell block is terminal). Then `G` lies in the join
`S^Z_M ⊔ S^X_M ⊔ L_M`. This is the reverse inclusion `N_M ⊆ ⟨S^Z_M, S^X_M, L_M⟩` of Theorem D.1
restricted to terminal layers — the endgame of the *reduction by multiplication* argument, whose
remaining task (Lemmas D.4–D.6) is to reduce an arbitrary `G ∈ N_M` to this terminal case.

The word `W = U_Z(B) L_X(C) U_Z(B)` lies in `S^Z_M ⊔ S^X_M` (`word_mem_sup_shearFamilyM`): from
terminality `B`, `C` are symmetric, from `G ∈ N_M` they are `M`-block-diagonal
(`isSpBlockDiagonal_fromBlocks_iff`) and valid (`C_X B ⊆ C_Z`, `C_Z C ⊆ C_X` by
`mem_codePreservingGroup_fromBlocks_iff`). The Levi cofactor `L* := G · W =
[[A + B C, 0], [0, D + C B]]` (`terminalBlock_mul_word`) is a Levi gate — its own symplectic
relations make `A + B C` a unit with inverse-transpose `D + C B` — and lies in `N_M` (a group), so
`L* ∈ L_M`. Since `W` is an involution, `G = L* · W`, exhibiting `G` in the join. -/
theorem terminalLayer_mem_sup_familyM {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)}
    {σ : Equiv.Perm ι} (hσ : Function.Involutive σ) {G : ↥(binarySymplecticGroup ι)}
    {A B C D : Matrix ι ι (ZMod 2)}
    (hG : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = Matrix.fromBlocks A B C D)
    (hmem : G ∈ fixedMatchingSlice C_X C_Z σ hσ)
    (hterm : IsTerminalBlock A B C D) :
    G ∈ shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ ⊔ leviFamilyM C_X C_Z σ hσ := by
  have hBsymm : (B : Matrix ι ι (ZMod 2)).IsSymm := hterm.isSymm_B
  have hCsymm : (C : Matrix ι ι (ZMod 2)).IsSymm := hterm.isSymm_C
  have hGsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι := hG ▸ G.2
  -- code-preservation and block-diagonality of `G` from `G ∈ N_M`
  have hN : G ∈ codePreservingGroup C_X C_Z := (mem_fixedMatchingSlice_iff.mp hmem).1
  have hG_bd : G ∈ blockDiagonalSymplecticGroup σ hσ :=
    fixedMatchingSlice_le_blockDiagonalSymplecticGroup C_X C_Z σ hσ hmem
  obtain ⟨_, hvB, hvC, _⟩ := (mem_codePreservingGroup_fromBlocks_iff hG).mp hN
  have hbd : IsCellDiagonal σ A ∧ IsCellDiagonal σ B ∧ IsCellDiagonal σ C ∧ IsCellDiagonal σ D := by
    rw [← isSpBlockDiagonal_fromBlocks_iff, ← hG]
    exact (mem_blockDiagonalSymplecticGroup_iff hσ).mp hG_bd
  obtain ⟨_, hcB, hcC, _⟩ := hbd
  -- `B` and `C` are admissible, `M`-block-diagonal parameters, so `W ∈ S^Z_M ⊔ S^X_M`
  have hBadm : B ∈ admissibleParamsBlockDiag C_X C_Z σ :=
    mem_admissibleParamsBlockDiag.mpr ⟨hBsymm, hvB, hcB⟩
  have hCadm : C ∈ admissibleParamsBlockDiag C_Z C_X σ :=
    mem_admissibleParamsBlockDiag.mpr ⟨hCsymm, hvC, hcC⟩
  set W : ↥(binarySymplecticGroup ι) :=
    ⟨word B C, word_mem_binarySymplecticGroup hBsymm hCsymm⟩ with hW
  have hWmem : W ∈ shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ :=
    word_mem_sup_shearFamilyM hσ hBadm hCadm rfl
  -- the coordinate form of the Levi cofactor `L* = G · W`
  have hLcoe : ((G * W : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
      = Matrix.fromBlocks (A + B * C) 0 0 (D + C * B) := by
    rw [Submonoid.coe_mul, hG]
    exact terminalBlock_mul_word hGsymp hterm
  -- `L*` is a Levi gate: its symplectic relations make `A + B C` a unit with inverse-transpose
  have hLsymp : Matrix.fromBlocks (A + B * C) 0 0 (D + C * B) ∈ binarySymplecticGroup ι := by
    rw [← hLcoe]; exact (G * W).2
  obtain ⟨_, _, _, _, hPQ0, _⟩ := fromBlocks_symplectic_relations hLsymp
  have hPQ : (A + B * C) * (D + C * B)ᵀ = 1 := by simpa using hPQ0
  have hQP : (D + C * B)ᵀ * (A + B * C) = 1 := mul_eq_one_comm.mp hPQ
  have hLevi : G * W ∈ leviGroup := by
    refine ⟨⟨A + B * C, (D + C * B)ᵀ, hPQ, hQP⟩, ?_⟩
    rw [hLcoe, leviGate]
    change Matrix.fromBlocks (A + B * C) 0 0 (D + C * B)
      = Matrix.fromBlocks (A + B * C) 0 0 ((D + C * B)ᵀ)ᵀ
    rw [Matrix.transpose_transpose]
  -- `L*` also lies in `N` and in `𝒟_M`, hence in `L_M`
  have hW_N : W ∈ codePreservingGroup C_X C_Z :=
    (sup_le (shearZFamilyM_le_codePreservingGroup C_X C_Z σ hσ)
      (shearXFamilyM_le_codePreservingGroup C_X C_Z σ hσ)) hWmem
  have hW_bd : W ∈ blockDiagonalSymplecticGroup σ hσ :=
    (mem_blockDiagonalSymplecticGroup_iff hσ).mpr
      (by rw [hW]; exact word_isSpBlockDiagonal hσ hcB hcC)
  have hLfam : G * W ∈ leviFamilyM C_X C_Z σ hσ := by
    rw [mem_leviFamilyM]
    exact ⟨mem_leviFamily.mpr ⟨hLevi, mul_mem hN hW_N⟩,
      (mem_blockDiagonalSymplecticGroup_iff hσ).mp (mul_mem hG_bd hW_bd)⟩
  -- rearrange `G = L* · W` (using `W W = 1`) into the join
  have hWW : W * W = 1 := by
    apply Subtype.ext
    rw [Submonoid.coe_mul, hW]
    exact word_mul_self B C
  have hGeq : G = (G * W) * W := by rw [mul_assoc, hWW, mul_one]
  rw [hGeq]
  exact mul_mem (Subgroup.mem_sup_right hLfam) (Subgroup.mem_sup_left hWmem)

end CliffordCSS

import CliffordCSS.DepthOne.LocalMove

/-!
# Beyond transversality (arXiv:2608.05688) — relabelling the local-move structure

Pure mathematics : the **coordinate-relabelling transport** of the
Lemma-D.4 apparatus of `BeyondTransversalityLocalMove.lean` along an arbitrary bijection
`e : κ ≃ κ'` of the cell index type.

`LocalReduction w k` (Lemma D.4) quantifies over *every* index type of cardinality `w`
(`∀ κ, Fintype.card κ = w → …`), but the finite verification that discharges it is inevitably run
over the concrete `Fin 2` block calculus of the packed enumeration (`CliffordCSS/Packed/Reaches.lean`,
`CliffordCSS/Packed/CliffordCompleteness.lean`). To close the gap between the two, everything in the
Lemma-D.4 machinery — symplectic membership, the terminal predicate, the block-move relation and
bounded reachability — must be shown **invariant under `e`**. That is what this file provides: with
`reBlk e` the block relabelling `Matrix κ κ 𝔽₂ ≃ₐ Matrix κ' κ' 𝔽₂` and `reSp e` the induced
relabelling of the `κ ⊕ κ` symplectic coordinates, it proves

* `reSp_fromBlocks` — the keystone `reSp e [[A,B],[C,D]] = [[reBlk e A, …], …]`, from which
  `reSp_symplecticMatrix`, `reSp_shearZ`/`reSp_shearX` and the parameter transport
  `layerZParam_reSp` / `layerXParam_reSp` all descend;
* `isTerminalLayer_reSp` — terminality is preserved
  (`IsTerminalLayer (reSp e g) ↔ IsTerminalLayer g`);
* `isBlockMove_reSp` — the move relation is preserved
  (`IsBlockMove (reSp e g) (reSp e g') ↔ IsBlockMove g g'`);
* `reachesTerminalIn_reSp` — bounded reachability is preserved
  (`ReachesTerminalIn k (reSp e g) ↔ ReachesTerminalIn k g`);
* `mem_binarySymplecticGroup_reSp` — symplectic-group membership is preserved
  (`reSp e g ∈ Sp(2·|κ'|, 𝔽₂) ↔ g ∈ Sp(2·|κ|, 𝔽₂)`).

Together (`mem_binarySymplecticGroup_reSp` and `reachesTerminalIn_reSp`) these reduce
`LocalReduction w k` at an *arbitrary* `κ` to the same statement at `Fin w` via
`e := Fintype.equivFinOfCardEq`, so the terminal width-two chunk need only feed the `Fin 2` packed
`decide` through them — the abstract-index transport (T2) is handled here, once, generically, rather
than being rediscovered at assembly time.

The relabelling map is Mathlib's `Matrix.reindexAlgEquiv` (an `AlgEquiv`, so it transports `*`, `+`,
`1`, `0` and the `𝔽₂`-action for free); only its interaction with `transpose`, `fromBlocks` and the
symplectic vocabulary needs bespoke lemmas.

Math-only (raw `Matrix` carriers);
names.
-/

open Matrix

namespace CliffordCSS

variable {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- **The block relabelling** `Matrix κ κ 𝔽₂ ≃ₐ Matrix κ' κ' 𝔽₂` induced by a bijection
`e : κ ≃ κ'` of the cell coordinates: Mathlib's `reindexAlgEquiv`, an algebra isomorphism, so it
carries `*`, `+`, `1`, `0` and the `𝔽₂`-action across `e`. -/
abbrev reBlk (e : κ ≃ κ') : Matrix κ κ (ZMod 2) ≃ₐ[ZMod 2] Matrix κ' κ' (ZMod 2) :=
  Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e

/-- **The symplectic-coordinate relabelling** `Matrix (κ ⊕ κ) 𝔽₂ ≃ₐ Matrix (κ' ⊕ κ') 𝔽₂` induced by
`e : κ ≃ κ'`, relabelling both the `X`- and the `Z`-halves of the `2·|κ|` coordinates by `e` via
`e.sumCongr e`. This is the map along which the whole Lemma-D.4 apparatus is transported. -/
abbrev reSp (e : κ ≃ κ') :
    Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2) ≃ₐ[ZMod 2] Matrix (κ' ⊕ κ') (κ' ⊕ κ') (ZMod 2) :=
  Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (e.sumCongr e)

variable (e : κ ≃ κ')

/-- Relabelling commutes with transpose on blocks: `reBlk e Mᵀ = (reBlk e M)ᵀ`. -/
theorem reBlk_transpose (M : Matrix κ κ (ZMod 2)) : reBlk e Mᵀ = (reBlk e M)ᵀ := by
  simp only [Matrix.reindexAlgEquiv_apply, Matrix.transpose_reindex]

/-- Relabelling commutes with transpose on the `κ ⊕ κ` coordinates: `reSp e Mᵀ = (reSp e M)ᵀ`. -/
theorem reSp_transpose (M : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) : reSp e Mᵀ = (reSp e M)ᵀ := by
  simp only [Matrix.reindexAlgEquiv_apply, Matrix.transpose_reindex]

/-- **The keystone.** Relabelling a block matrix relabels each of its four blocks:
`reSp e [[A, B], [C, D]] = [[reBlk e A, reBlk e B], [reBlk e C, reBlk e D]]`. Everything downstream
(the symplectic Gram matrix, the shears, the move parameters, terminality) is expressed through
`fromBlocks`, so this single compatibility drives all of the transport lemmas below. -/
theorem reSp_fromBlocks (A B C D : Matrix κ κ (ZMod 2)) :
    reSp e (Matrix.fromBlocks A B C D)
      = Matrix.fromBlocks (reBlk e A) (reBlk e B) (reBlk e C) (reBlk e D) := by
  simp only [Matrix.reindexAlgEquiv_apply]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply]

/-- The symplectic Gram matrix `Λ = [[0, I], [I, 0]]` is fixed by relabelling:
`reSp e symplecticMatrix = symplecticMatrix`. -/
theorem reSp_symplecticMatrix : reSp e (symplecticMatrix : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2))
    = symplecticMatrix := by
  rw [symplecticMatrix, reSp_fromBlocks, map_zero, map_one, symplecticMatrix]

/-- Relabelling carries the `Z`-shear `U_Z(S) = [[I, S], [0, I]]` to `U_Z(reBlk e S)`. -/
theorem reSp_shearZ (S : Matrix κ κ (ZMod 2)) : reSp e (shearZ S) = shearZ (reBlk e S) := by
  rw [shearZ, reSp_fromBlocks, map_one, map_zero, shearZ]

/-- Relabelling carries the `X`-shear `L_X(T) = [[I, 0], [T, I]]` to `L_X(reBlk e T)`. -/
theorem reSp_shearX (T : Matrix κ κ (ZMod 2)) : reSp e (shearX T) = shearX (reBlk e T) := by
  rw [shearX, reSp_fromBlocks, map_one, map_zero, shearX]

/-- The `Z`-parameter formula transports: `reBlk e (S^Z(A, B, D, ε)) = S^Z(reBlk e A, …, ε)`. Each
generator `A Bᵀ`, `Dᵀ B`, `B + Bᵀ` is a product/sum/transpose of blocks, all carried by the
algebra isomorphism `reBlk e` (with `reBlk_transpose` for the transposes). -/
theorem reBlk_spzParam (A B D : Matrix κ κ (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    reBlk e (spzParam A B D ε) = spzParam (reBlk e A) (reBlk e B) (reBlk e D) ε := by
  simp only [spzParam, map_add, map_smul, map_mul, reBlk_transpose]

/-- The `X`-parameter formula transports (dual to `reBlk_spzParam`):
`reBlk e (S^X(A, C, D, ε)) = S^X(reBlk e A, …, ε)`. -/
theorem reBlk_spxParam (A C D : Matrix κ κ (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    reBlk e (spxParam A C D ε) = spxParam (reBlk e A) (reBlk e C) (reBlk e D) ε := by
  simp only [spxParam, map_add, map_smul, map_mul, reBlk_transpose]

/-- The manufactured `Z`-parameter of the relabelled block is the relabelling of the parameter:
`layerZParam (reSp e g) ε = reBlk e (layerZParam g ε)`. -/
theorem layerZParam_reSp (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    layerZParam (reSp e g) ε = reBlk e (layerZParam g ε) := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [reSp_fromBlocks, layerZParam_fromBlocks, layerZParam_fromBlocks, reBlk_spzParam]

/-- The manufactured `X`-parameter of the relabelled block is the relabelling of the parameter
(dual to `layerZParam_reSp`). -/
theorem layerXParam_reSp (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    layerXParam (reSp e g) ε = reBlk e (layerXParam g ε) := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [reSp_fromBlocks, layerXParam_fromBlocks, layerXParam_fromBlocks, reBlk_spxParam]

/-- A relabelled block is nonzero iff the block is (`reBlk e` is injective and `𝔽₂`-linear). The
"nonzero parameter" side condition of a move is therefore invariant. -/
theorem reBlk_eq_zero_iff (M : Matrix κ κ (ZMod 2)) : reBlk e M = 0 ↔ M = 0 :=
  map_eq_zero_iff _ (AlgEquiv.injective _)

/-- **Terminality is invariant under relabelling**:
`IsTerminalLayer (reSp e g) ↔ IsTerminalLayer g`.
Each of the six conjuncts of Eq. (d1-term) is `<block expression> = 0`, and `reBlk e` is an
injective `𝔽₂`-algebra map, so each holds for the relabelled blocks iff for the originals. -/
theorem isTerminalLayer_reSp (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) :
    IsTerminalLayer (reSp e g) ↔ IsTerminalLayer g := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [reSp_fromBlocks, isTerminalLayer_fromBlocks, isTerminalLayer_fromBlocks]
  simp only [IsTerminalBlock, ← reBlk_transpose, ← map_mul, ← map_add, reBlk_eq_zero_iff]

/-- **The block-move relation is invariant under relabelling**:
`IsBlockMove (reSp e g) (reSp e g') ↔ IsBlockMove g g'`. Each move is a nonzero manufactured
parameter and a left/right shear multiplication; the parameter transports (`layerZParam_reSp`), the
shear transports (`reSp_shearZ`), multiplication is carried by `reSp e`, and `reSp e` is injective,
so the whole relation matches under relabelling. -/
theorem isBlockMove_reSp (g g' : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) :
    IsBlockMove (reSp e g) (reSp e g') ↔ IsBlockMove g g' := by
  unfold IsBlockMove
  refine or_congr (exists_congr fun ε => and_congr ?_ (or_congr ?_ ?_))
    (exists_congr fun ε => and_congr ?_ (or_congr ?_ ?_))
  · rw [layerZParam_reSp, ne_eq, ne_eq, reBlk_eq_zero_iff]
  · rw [layerZParam_reSp, ← reSp_shearZ, ← map_mul, EmbeddingLike.apply_eq_iff_eq]
  · rw [layerZParam_reSp, ← reSp_shearZ, ← map_mul, EmbeddingLike.apply_eq_iff_eq]
  · rw [layerXParam_reSp, ne_eq, ne_eq, reBlk_eq_zero_iff]
  · rw [layerXParam_reSp, ← reSp_shearX, ← map_mul, EmbeddingLike.apply_eq_iff_eq]
  · rw [layerXParam_reSp, ← reSp_shearX, ← map_mul, EmbeddingLike.apply_eq_iff_eq]

/-- **Bounded reachability is invariant under relabelling**:
`ReachesTerminalIn k (reSp e g) ↔ ReachesTerminalIn k g`. By induction on `k` from the terminal
(`isTerminalLayer_reSp`) and move (`isBlockMove_reSp`) invariances; the existential over the next
block is transported by the surjectivity of `reSp e` (`AlgEquiv.apply_symm_apply`). -/
theorem reachesTerminalIn_reSp (k : ℕ) (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) :
    ReachesTerminalIn k (reSp e g) ↔ ReachesTerminalIn k g := by
  induction k generalizing g with
  | zero => simpa only [reachesTerminalIn_zero] using isTerminalLayer_reSp e g
  | succ k ih =>
    rw [reachesTerminalIn_succ, reachesTerminalIn_succ]
    refine or_congr (isTerminalLayer_reSp e g) ?_
    constructor
    · rintro ⟨h', hmove, hreach⟩
      refine ⟨(reSp e).symm h', ?_, ?_⟩
      · rw [← isBlockMove_reSp e g ((reSp e).symm h'), AlgEquiv.apply_symm_apply]
        exact hmove
      · rw [← ih ((reSp e).symm h'), AlgEquiv.apply_symm_apply]
        exact hreach
    · rintro ⟨h, hmove, hreach⟩
      exact ⟨reSp e h, (isBlockMove_reSp e g h).mpr hmove, (ih h).mpr hreach⟩

/-- **Symplectic-group membership is invariant under relabelling**:
`reSp e g ∈ Sp(2·|κ'|, 𝔽₂) ↔ g ∈ Sp(2·|κ|, 𝔽₂)`. The defining condition
`G Λ Gᵀ = Λ` (`mem_binarySymplecticGroup_iff`) is transported by `reSp e`, which carries `*`,
transpose (`reSp_transpose`) and the Gram matrix (`reSp_symplecticMatrix`), and is injective. -/
theorem mem_binarySymplecticGroup_reSp (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) :
    reSp e g ∈ binarySymplecticGroup κ' ↔ g ∈ binarySymplecticGroup κ := by
  rw [mem_binarySymplecticGroup_iff, mem_binarySymplecticGroup_iff,
    ← reSp_symplecticMatrix e, ← reSp_transpose]
  simp only [← map_mul]
  rw [EmbeddingLike.apply_eq_iff_eq]

end CliffordCSS

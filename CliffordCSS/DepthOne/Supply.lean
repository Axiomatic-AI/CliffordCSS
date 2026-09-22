import CliffordCSS.DepthOne.CodePreserving
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Supply lemmas for the fixed-matching generation theorem (Beyond transversality, App. D)

Pure mathematics : the **supply** layer of §D.1 of *Beyond
transversality* (arXiv:2608.05688) — the elementary `𝔽₂`-symplectic facts that "manufacture the
moves" for the fixed-matching generation theorem (Theorem D.1). Everything is `𝔽₂` symplectic linear
algebra naming the raw carrier `Matrix`.

## The paper's setup (§D.1, "Validity and automatically valid diagonal circuits")

For a symplectic block matrix `G = [[A, B], [C, D]] ∈ Sp(2n, 𝔽₂)`:

* **Symplectic block relations (Eq. d1-sympl).** Expanding `G J Gᵀ = J` and `Gᵀ J G = J` in blocks,
  `A Bᵀ`, `C Dᵀ`, `Aᵀ C`, `Bᵀ D` are symmetric and `A Dᵀ + B Cᵀ = I`, `Aᵀ D + Cᵀ B = I`.
* **Inverse formula (Eq. d1-inv).** Over `𝔽₂`, `G⁻¹ = J Gᵀ J = [[Dᵀ, Bᵀ], [Cᵀ, Aᵀ]]` (the sign in
  `G⁻¹ = -J Gᵀ J` vanishes since `-1 = 1`).
* **Validity characterization (Eq. d1-valid).** Preservation of the CSS-form label space
  `𝒞 = (C_X | 0) ⊕ (0 | C_Z)`, i.e. `G ∈ N = Stab(𝒞)`, is *equivalent* to the four block inclusions
  `C_X A ⊆ C_X`, `C_X B ⊆ C_Z`, `C_Z C ⊆ C_X`, `C_Z D ⊆ C_Z`. The forward direction feeds `(c | 0)`
  with `c ∈ C_X` and `(0 | d)` with `d ∈ C_Z` into `G` (Convention c2 right action). For the
  reverse, *inclusions suffice*: the four inclusions give the one-directional `𝒞 G ⊆ 𝒞`, and,
  `G` being invertible, the map `v ↦ v ᵥ* G` preserves the finite dimension of `𝒞`, so
  `𝒞 G ⊆ 𝒞` forces `𝒞 G = 𝒞`, hence the two-sided membership defining `N`.

Following the paper, no orthogonality `C_X ⊥ C_Z` is assumed — "a statement about split subspaces
and nothing more".

## What is proved

* `fromBlocks_symplectic_relations` — Eq. (d1-sympl), all six relations collected (from the two
  block readings `fromBlocks_mem_binarySymplecticGroup_iff` / `…_iff'` in `BinarySymplecticGroup`).
* `coe_inv_eq_fromBlocks` — Eq. (d1-inv), `G⁻¹ = [[Dᵀ, Bᵀ], [Cᵀ, Aᵀ]]`.
* `mem_codePreservingGroup_fromBlocks_iff` — Eq. (d1-valid), the validity block-inclusion
  characterization of `N` (the defining API of the code-preserving group).
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Symplectic block relations (Eq. d1-sympl)

The two block readings of the symplectic condition — `fromBlocks_mem_binarySymplecticGroup_iff`
(from `G J Gᵀ = J`) and `fromBlocks_mem_binarySymplecticGroup_iff'` (from `Gᵀ J G = J`) — live
beside each other in `CliffordCSS/Symplectic/Group.lean`; here we collect them into
Eq. (d1-sympl). -/

/-- **Eq. (d1-sympl).** Collecting both readings of the symplectic condition for
`G = [[A, B], [C, D]] ∈ Sp(2n, 𝔽₂)`: the four block products `A Bᵀ`, `C Dᵀ`, `Aᵀ C`, `Bᵀ D` are
symmetric, and `A Dᵀ + B Cᵀ = I`, `Aᵀ D + Cᵀ B = I`. These are the relations the automatic-parameter
construction (Lemma D.2) reads its symmetries off of. -/
theorem fromBlocks_symplectic_relations {A B C D : Matrix ι ι (ZMod 2)}
    (hG : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι) :
    A * Bᵀ = B * Aᵀ ∧ C * Dᵀ = D * Cᵀ ∧ Aᵀ * C = Cᵀ * A ∧ Bᵀ * D = Dᵀ * B ∧
      A * Dᵀ + B * Cᵀ = 1 ∧ Aᵀ * D + Cᵀ * B = 1 := by
  obtain ⟨h1, h2, h3⟩ := (fromBlocks_mem_binarySymplecticGroup_iff A B C D).mp hG
  obtain ⟨h4, h5, h6⟩ := (fromBlocks_mem_binarySymplecticGroup_iff' A B C D).mp hG
  exact ⟨h1, h2, h4, h5, h3, h6⟩

/-! ### Inverse formula (Eq. d1-inv) -/

/-- **Eq. (d1-inv).** Over `𝔽₂` the inverse of a symplectic block matrix `G = [[A, B], [C, D]]` is
`G⁻¹ = [[Dᵀ, Bᵀ], [Cᵀ, Aᵀ]]`. Indeed `G⁻¹ = J Gᵀ J` (the sign in Mathlib's `-J Gᵀ J` vanishes since
`-1 = 1`), and `J [[Aᵀ, Cᵀ], [Bᵀ, Dᵀ]] J = [[Dᵀ, Bᵀ], [Cᵀ, Aᵀ]]`. -/
theorem coe_inv_eq_fromBlocks {G : ↥(binarySymplecticGroup ι)} {A B C D : Matrix ι ι (ZMod 2)}
    (hG : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = Matrix.fromBlocks A B C D) :
    ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
      = Matrix.fromBlocks Dᵀ Bᵀ Cᵀ Aᵀ := by
  rw [SymplecticGroup.coe_inv, hG, neg_eq_self_zmod2, J_eq_symplecticMatrix, symplecticMatrix,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [zero_mul, one_mul, mul_zero, mul_one, zero_add, add_zero]

/-! ### Validity characterization (Eq. d1-valid) -/

/-- **Eq. (d1-valid): the validity block-inclusion characterization of `N`.** For a symplectic block
matrix `G = [[A, B], [C, D]]` (via `hG : ↑G = [[A, B], [C, D]]`), membership in the code-preserving
group `N = Stab(𝒞)` of `𝒞 = (C_X | 0) ⊕ (0 | C_Z)` is equivalent to the four block inclusions
`C_X A ⊆ C_X`, `C_X B ⊆ C_Z`, `C_Z C ⊆ C_X`, `C_Z D ⊆ C_Z` (the row-vector action `x ↦ x ᵥ* ·` of
Convention c2). This is the defining API of `N`: the forward direction feeds `(c | 0)` and `(0 | d)`
into `G`; the reverse turns the resulting one-directional `𝒞 G ⊆ 𝒞` into the two-sided
setwise-stabilizer condition using that `v ↦ v ᵥ* G` is a linear automorphism preserving the finite
dimension of `𝒞` (invertibility upgrades `⊆` to `=`). -/
theorem mem_codePreservingGroup_fromBlocks_iff {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)}
    {G : ↥(binarySymplecticGroup ι)} {A B C D : Matrix ι ι (ZMod 2)}
    (hG : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = Matrix.fromBlocks A B C D) :
    G ∈ codePreservingGroup C_X C_Z ↔
      (∀ x ∈ C_X, Matrix.vecMul x A ∈ C_X) ∧ (∀ x ∈ C_X, Matrix.vecMul x B ∈ C_Z) ∧
        (∀ z ∈ C_Z, Matrix.vecMul z C ∈ C_X) ∧ (∀ z ∈ C_Z, Matrix.vecMul z D ∈ C_Z) := by
  constructor
  · -- Forward: feed `(x | 0)` and `(0 | z)` into `G`.
    intro hmem
    have key : ∀ x z : ι → ZMod 2, x ∈ C_X → z ∈ C_Z →
        Matrix.vecMul x A + Matrix.vecMul z C ∈ C_X ∧
          Matrix.vecMul x B + Matrix.vecMul z D ∈ C_Z := by
      intro x z hx hz
      have hv : (Sum.elim x z : ι ⊕ ι → ZMod 2) ∈ cssLabelSpaceSum C_X C_Z := by
        rw [mem_cssLabelSpaceSum]
        exact ⟨by simpa using hx, by simpa using hz⟩
      have h2 := (mem_codePreservingGroup_iff.mp hmem (Sum.elim x z)).mp hv
      rw [hG, vecMul_fromBlocks_blocks, mem_cssLabelSpaceSum] at h2
      simpa using h2
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · simpa using (key x 0 hx C_Z.zero_mem).1
    · simpa using (key x 0 hx C_Z.zero_mem).2
    · simpa using (key 0 z C_X.zero_mem hz).1
    · simpa using (key 0 z C_X.zero_mem hz).2
  · -- Reverse: inclusions ⟹ one-directional `𝒞 G ⊆ 𝒞`, then upgrade via invertibility.
    rintro ⟨h1, h2, h3, h4⟩
    -- The one-directional forward inclusion `∀ v ∈ 𝒞, v ᵥ* G ∈ 𝒞`.
    have hfwd : ∀ v ∈ cssLabelSpaceSum C_X C_Z,
        v ᵥ* (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∈ cssLabelSpaceSum C_X C_Z := by
      intro v hv
      rw [mem_cssLabelSpaceSum] at hv
      obtain ⟨hvX, hvZ⟩ := hv
      have hsplit : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by funext p; cases p <;> rfl
      rw [mem_cssLabelSpaceSum, hG]
      have hcomp : v ᵥ* Matrix.fromBlocks A B C D
          = Sum.elim (Matrix.vecMul (v ∘ Sum.inl) A + Matrix.vecMul (v ∘ Sum.inr) C)
              (Matrix.vecMul (v ∘ Sum.inl) B + Matrix.vecMul (v ∘ Sum.inr) D) := by
        conv_lhs => rw [hsplit]
        rw [vecMul_fromBlocks_blocks]
      rw [hcomp]
      exact ⟨by simpa using C_X.add_mem (h1 _ hvX) (h3 _ hvZ),
        by simpa using C_Z.add_mem (h2 _ hvX) (h4 _ hvZ)⟩
    -- The linear automorphism `e : v ↦ v ᵥ* G`, invertible because `G` is a group element.
    have hMM' : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) *
        ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
    have hM'M : ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) *
        (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
    let e : (ι ⊕ ι → ZMod 2) ≃ₗ[ZMod 2] (ι ⊕ ι → ZMod 2) :=
      LinearEquiv.ofLinear
        (Matrix.vecMulLinear (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))
        (Matrix.vecMulLinear ((G⁻¹ : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))
        (LinearMap.ext fun v => by
          simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.vecMulLinear_apply,
            Matrix.vecMul_vecMul, hM'M, Matrix.vecMul_one])
        (LinearMap.ext fun v => by
          simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.vecMulLinear_apply,
            Matrix.vecMul_vecMul, hMM', Matrix.vecMul_one])
    have he : ∀ x, e x = x ᵥ* (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) := fun _ => rfl
    -- `𝒞.map e ≤ 𝒞` from `hfwd`, upgraded to `𝒞.map e = 𝒞` by finite-dimension preservation.
    have hle : (cssLabelSpaceSum C_X C_Z).map
        (e : (ι ⊕ ι → ZMod 2) →ₗ[ZMod 2] (ι ⊕ ι → ZMod 2)) ≤ cssLabelSpaceSum C_X C_Z := by
      rintro _ ⟨v, hv, rfl⟩
      simpa only [LinearEquiv.coe_coe, he] using hfwd v hv
    have hmap : (cssLabelSpaceSum C_X C_Z).map
        (e : (ι ⊕ ι → ZMod 2) →ₗ[ZMod 2] (ι ⊕ ι → ZMod 2)) = cssLabelSpaceSum C_X C_Z :=
      Submodule.eq_of_le_of_finrank_le hle (le_of_eq (LinearEquiv.finrank_map_eq e _).symm)
    -- Assemble the two-sided setwise-stabilizer condition defining `N`.
    rw [mem_codePreservingGroup_iff]
    intro v
    constructor
    · intro hv; exact hfwd v hv
    · intro hv
      have hev : e v ∈ cssLabelSpaceSum C_X C_Z := by rw [he]; exact hv
      rw [← hmap, Submodule.mem_map_equiv] at hev
      simpa using hev

end CliffordCSS

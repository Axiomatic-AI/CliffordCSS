import CliffordCSS.DepthOne.BlockDiagonal

/-!
# The code-preserving group `N = Stab_{Sp(2n)}(𝒞)` (Beyond transversality, App. D.1)

Pure mathematics : the **code-preserving group**
`N = Stab_{Sp(2n)}(𝒞)` of *Beyond transversality* (arXiv:2608.05688) Appendix D, and its **two-fold
transversal slice** `N_M := 𝒟_M ∩ N` (Eq. (D1)). These are the ambient objects of the fixed-matching
generation theorem (Theorem D.1, `thm-depthone`): `N_M = ⟨S^Z_M, S^X_M, L_M⟩`.

All of Appendix D is `𝔽₂`-symplectic linear algebra naming the raw carrier `Matrix`.

## The paper's setup (§D.1, Convention c5)

The phase space `V = 𝔽₂^{2n}` of `n = |ι|` qubits carries the CSS-form label space
`𝒞 = (C_X | 0) ⊕ (0 | C_Z)` (Convention c1) of a pair of classical binary codes `C_X`, `C_Z`. The
binary symplectic group `Sp(2n, 𝔽₂) = binarySymplecticGroup` acts on row vectors from the right by
`Matrix.vecMul` (Convention c2). The **code-preserving group** is the setwise stabilizer of `𝒞`
under this action,
`N = Stab_{Sp(2n)}(𝒞) = { G ∈ Sp(2n) : 𝒞 · G = 𝒞 }`,
and, for a matching `M` given by an involution `σ`, its **two-fold transversal slice** is
`N_M := 𝒟_M ∩ N` (Eq. (D1)), the intersection with the `M`-block-diagonal symplectic subgroup
`𝒟_M = blockDiagonalSymplecticGroup`.

Following the paper, no orthogonality `C_X ⊥ C_Z` is assumed: the objects are stated for an
arbitrary pair of `𝔽₂`-subspaces `C_X`, `C_Z` — "a statement about split subspaces and nothing
more".

## Encoding of `𝒞`, and of the setwise stabilizer

The symplectic group is indexed by `ι ⊕ ι` (the polarized `X | Z` split), so a label vector is
`v : ι ⊕ ι → ZMod 2`, whose `X`-part is `v ∘ Sum.inl` and `Z`-part `v ∘ Sum.inr`. Accordingly `𝒞`
is `cssLabelSpaceSum C_X C_Z`, the subspace of `v` with `v ∘ Sum.inl ∈ C_X` and `v ∘ Sum.inr ∈ C_Z`.

The **setwise** stabilizer `𝒞 · G = 𝒞` is encoded as the two-sided membership condition
`∀ v, v ∈ 𝒞 ↔ v ᵥ* G ∈ 𝒞` — for the *bijective* map `v ↦ v ᵥ* G` (`G` lies in a group) this is
exactly `(v ↦ v ᵥ* G)(𝒞) = 𝒞`, and it is manifestly closed under the group operations (identity,
product, and — crucially, with no dimension argument — inverse), giving `N` as a genuine `Subgroup`.
The concrete block-inclusion characterization "`G ∈ N ⟺ C_X A ⊆ C_X`, `C_X B ⊆ C_Z`, …", which needs
the invertibility-upgrades-`⊆`-to-`=` argument, is separate
supply content built on top of this.

## What is defined and proved

* `cssLabelSpaceSum` — the CSS-form label space `𝒞` in the sum coordinates `ι ⊕ ι` the symplectic
  group acts on, with membership lemma `mem_cssLabelSpaceSum`.
* `codePreservingGroup` — `N = Stab_{Sp(2n)}(𝒞)`, as a `Subgroup` of `binarySymplecticGroup`, with
  membership lemma `mem_codePreservingGroup_iff`.
* `fixedMatchingSlice` — `N_M := N ∩ 𝒟_M`, with membership lemmas `mem_fixedMatchingSlice_iff` and
  `mem_fixedMatchingSlice_iff'` (the paper's `𝒟_M ∩ N` reading).
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The CSS-form **label space** `𝒞 = (C_X | 0) ⊕ (0 | C_Z)` (Convention c1) in the sum coordinates
`ι ⊕ ι` on which the binary symplectic group acts: the subspace of label vectors
`v : ι ⊕ ι → ZMod 2` whose pure-`X` part `v ∘ Sum.inl` lies in `C_X` and whose pure-`Z` part
`v ∘ Sum.inr` lies in `C_Z`. This is the sum-coordinate presentation of the product-coordinate
product-coordinate presentation (`v ↔ (v ∘ Sum.inl, v ∘ Sum.inr)` under
`Equiv.sumArrowEquivProdArrow`), used here because the symplectic action `v ᵥ* G` is on `ι ⊕ ι`. -/
def cssLabelSpaceSum (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule (ZMod 2) (ι ⊕ ι → ZMod 2) :=
  C_X.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inl : ι → ι ⊕ ι))
    ⊓ C_Z.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inr : ι → ι ⊕ ι))

omit [Fintype ι] [DecidableEq ι] in
/-- Membership in the CSS label space: `v ∈ 𝒞` iff its `X`-part `v ∘ Sum.inl` lies in `C_X` and its
`Z`-part `v ∘ Sum.inr` lies in `C_Z`. -/
@[simp] theorem mem_cssLabelSpaceSum {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)}
    {v : ι ⊕ ι → ZMod 2} :
    v ∈ cssLabelSpaceSum C_X C_Z ↔ (v ∘ Sum.inl) ∈ C_X ∧ (v ∘ Sum.inr) ∈ C_Z :=
  Iff.rfl

/-- The **code-preserving group** `N = Stab_{Sp(2n)}(𝒞)` of *Beyond transversality* (§D.1): the
subgroup of the binary symplectic group `Sp(2n, 𝔽₂)` (`binarySymplecticGroup`) that setwise
stabilizes the CSS label space `𝒞`, i.e. `𝒞 · G = 𝒞` under the right action `v ↦ v ᵥ* G`.

The setwise condition is encoded as the two-sided membership equivalence `∀ v, v ∈ 𝒞 ↔ v ᵥ* G ∈ 𝒞`.
For `G` in the group the map `v ↦ v ᵥ* G` is a bijection, so this equivalence says exactly that its
image of `𝒞` is `𝒞`. It is a genuine subgroup with no dimension argument: the identity acts
trivially (`v ᵥ* 1 = v`), a product chains the two equivalences (`v ᵥ* (G * H) = (v ᵥ* G) ᵥ* H`),
and the inverse follows because `(v ᵥ* G⁻¹) ᵥ* G = v ᵥ* (G⁻¹ * G) = v` reduces `G⁻¹`'s
equivalence to the reverse of `G`'s. -/
def codePreservingGroup (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)) :
    Subgroup ↥(binarySymplecticGroup ι) where
  carrier := {G |
    ∀ v, v ∈ cssLabelSpaceSum C_X C_Z ↔
      v ᵥ* (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∈ cssLabelSpaceSum C_X C_Z}
  one_mem' := by
    intro v
    rw [Submonoid.coe_one, Matrix.vecMul_one]
  mul_mem' {G H} hG hH := by
    intro v
    rw [Submonoid.coe_mul, ← Matrix.vecMul_vecMul, hG v, hH _]
  inv_mem' {G} hG := by
    intro v
    have hgg : ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
        * (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
    have key := hG
      (v ᵥ* ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))
    rw [Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one] at key
    exact key.symm

/-- Membership in the code-preserving group: `G ∈ N` iff `G` setwise stabilizes `𝒞`, i.e. for every
label vector `v`, `v ∈ 𝒞 ⟺ v ᵥ* G ∈ 𝒞`. -/
theorem mem_codePreservingGroup_iff {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)}
    {G : ↥(binarySymplecticGroup ι)} :
    G ∈ codePreservingGroup C_X C_Z ↔
      ∀ v, v ∈ cssLabelSpaceSum C_X C_Z ↔
        v ᵥ* (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∈ cssLabelSpaceSum C_X C_Z :=
  Iff.rfl

/-- The **two-fold transversal slice** `N_M := N ∩ 𝒟_M` of *Beyond transversality* (Eq. (D1)): the
code-preserving matrices that are in addition `M`-block-diagonal (depth-one `2`-local), for a
matching `M` given by an involution `σ`. Equal to the paper's `𝒟_M ∩ N` by commutativity of `⊓`
(`mem_fixedMatchingSlice_iff'`). -/
def fixedMatchingSlice (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2))
    (σ : Equiv.Perm ι) (hσ : Function.Involutive σ) :
    Subgroup ↥(binarySymplecticGroup ι) :=
  codePreservingGroup C_X C_Z ⊓ blockDiagonalSymplecticGroup σ hσ

/-- Membership in the two-fold transversal slice: `G ∈ N_M` iff `G` is code-preserving and
`M`-block-diagonal. -/
theorem mem_fixedMatchingSlice_iff {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)}
    {σ : Equiv.Perm ι} {hσ : Function.Involutive σ} {G : ↥(binarySymplecticGroup ι)} :
    G ∈ fixedMatchingSlice C_X C_Z σ hσ ↔
      G ∈ codePreservingGroup C_X C_Z ∧
        IsSpBlockDiagonal σ (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) := by
  rw [fixedMatchingSlice, Subgroup.mem_inf, mem_blockDiagonalSymplecticGroup_iff]


/-- The two-fold transversal slice is contained in the code-preserving group, `N_M ≤ N`. -/
theorem fixedMatchingSlice_le_codePreservingGroup
    (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2))
    (σ : Equiv.Perm ι) (hσ : Function.Involutive σ) :
    fixedMatchingSlice C_X C_Z σ hσ ≤ codePreservingGroup C_X C_Z :=
  inf_le_left

/-- The two-fold transversal slice is contained in the `M`-block-diagonal symplectic subgroup,
`N_M ≤ 𝒟_M`. -/
theorem fixedMatchingSlice_le_blockDiagonalSymplecticGroup
    (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2))
    (σ : Equiv.Perm ι) (hσ : Function.Involutive σ) :
    fixedMatchingSlice C_X C_Z σ hσ ≤ blockDiagonalSymplecticGroup σ hσ :=
  inf_le_right

end CliffordCSS

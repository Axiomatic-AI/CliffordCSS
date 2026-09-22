import CliffordCSS.Symplectic.CheckMatrixSymplectic
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The binary symplectic group `Sp(2n, 𝔽₂)` (Beyond transversality, App. D)

Pure mathematics : the **binary symplectic group** `Sp(2n)` over
`𝔽₂ = ZMod 2`, the object of study of Appendix D of *Beyond transversality*. The appendix is, in its
own words, "a statement about split subspaces and nothing more" — pure `𝔽₂` symplectic linear
algebra.

## The paper's setup (App. B/D, statement `def-binary-symplectic-group`, Convention c2)

The phase space of `n` qubits is `V = 𝔽₂^{2n}` with the fixed polarization `V = X̂ ⊕ Ẑ` into
pure-`X` and pure-`Z` labels; a vector is `(x | z)`, `x, z ∈ 𝔽₂^n`. We model the `2n` coordinates
by `ι ⊕ ι` (with `n = |ι|`), so `(x | z) = Sum.elim x z`. The symplectic form is
`⟨(x|z), (x'|z')⟩ = x·z' + z·x' = (x|z) J (x'|z')ᵀ` with Gram matrix `J = [[0, I], [I, 0]]`
(Eq. setup-form). Over `𝔽₂` this is exactly the matrix already named `CliffordCSS.symplecticMatrix`
(Nielsen & Chuang's `Λ`, eq. (10.84)): Mathlib's canonical `Matrix.J` is `[[0, -I], [I, 0]]`, and
`-1 = 1` in characteristic two, so the two coincide (`J_eq_symplecticMatrix`).

A symplectic matrix is written in the block form `G = [[A, B], [C, D]]` and acts on row vectors from
the **right**, `(x | z) G = (xA + zC | xB + zD)` (Convention c2, Eq. setup-blocks) — this is
`Matrix.vecMul` (`vecMul_fromBlocks_blocks`). Being symplectic means preserving the form, so
`G ∈ Sp(2n)` iff `G J Gᵀ = J`, equivalently `Gᵀ J G = J` (Eq. setup-symplectic;
`mem_binarySymplecticGroup_iff` / `mem_binarySymplecticGroup_iff'`). Written out in blocks the first
reading is `A Bᵀ = B Aᵀ`, `C Dᵀ = D Cᵀ`, `A Dᵀ + B Cᵀ = I` (Eq. setup-blockeqs;
`fromBlocks_mem_binarySymplecticGroup_iff`).

## What is proved

* `binarySymplecticGroup` — `Sp(2n, 𝔽₂) = Matrix.symplecticGroup ι (ZMod 2)`, the object of study.
* `symplecticMatrix_mem_binarySymplecticGroup` — the Gram matrix is itself symplectic
  (Mathlib's `SymplecticGroup.J_mem` in the `𝔽₂` spelling).
* `J_eq_symplecticMatrix` — the paper's Gram matrix `[[0, I], [I, 0]]` is Mathlib's `Matrix.J` over
  `𝔽₂` (they differ only by the sign `-1 = 1`), tying the two treatments together.
* `mem_binarySymplecticGroup_iff` / `mem_binarySymplecticGroup_iff'` — the defining condition
  `G J Gᵀ = J` and its equivalent `Gᵀ J G = J`, in the paper's `J`.
* `symplecticForm_vecMul_eq_dotProduct` — the transported form as a bilinear expression in the
  conjugate: `⟨u ᵥ* M, v ᵥ* M⟩ = u ⬝ᵥ (M J Mᵀ) *ᵥ v`.
* `mem_binarySymplecticGroup_iff_symplecticForm_vecMul` — the **form-side** membership criterion,
  `G ∈ Sp(2n, 𝔽₂) ↔ G preserves ⟨·,·⟩ under the right row action`. The definition-facing reading,
  complementing the block equations below: `mpr` is the entry point for a matrix arising from an
  action known to preserve the form, `mp` the exit point for a consumer of an established
  membership.
* `vecMul_fromBlocks_blocks` — Convention c2's right action `(x | z) G = (xA + zC | xB + zD)`.
* `fromBlocks_mem_binarySymplecticGroup_iff` — the block equations Eq. setup-blockeqs (first
  reading, from `G J Gᵀ = J`).
* `fromBlocks_mem_binarySymplecticGroup_iff'` — the second reading (from `Gᵀ J G = J`): `Aᵀ C`,
  `Bᵀ D` symmetric and `Aᵀ D + Cᵀ B = I`, via transpose-closure of the group.

Reuse: the Gram matrix `[[0, I], [I, 0]]` is the existing `CliffordCSS.symplecticMatrix`; the
membership conditions are Mathlib's `SymplecticGroup.mem_iff` / `mem_iff'` over that `J`; the right
action and block computations are Mathlib's `Matrix.vecMul_fromBlocks` / `fromBlocks_multiply` /
`fromBlocks_transpose` / `fromBlocks_inj`. Everything is over `𝔽₂`, matching the paper.
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over `𝔽₂ = ZMod 2` negation is the identity on matrices: `-Y = Y` (characteristic two). The
reusable char-2 fact behind `J_eq_symplecticMatrix` (`-I = I`) and the symmetric-product form of the
block equations (`X + Y = 0 ↔ X = Y`); it needs neither `Fintype` nor `DecidableEq`. -/
theorem neg_eq_self_zmod2 {ι : Type*} (Y : Matrix ι ι (ZMod 2)) : -Y = Y := by
  ext i j; simp [CharTwo.neg_eq]

/-- The **binary symplectic group** `Sp(2n, 𝔽₂)` of *Beyond transversality* (App. D): the `2n × 2n`
matrices over `𝔽₂ = ZMod 2` (with `n = |ι|`, the `2n` coordinates indexed by `ι ⊕ ι`) that preserve
the symplectic form, i.e. Mathlib's `Matrix.symplecticGroup ι (ZMod 2)`. Its defining membership
condition in the paper's Gram matrix `J = [[0, I], [I, 0]]` is `mem_binarySymplecticGroup_iff`.

An `abbrev` (like Mathlib's own `Matrix.orthogonalGroup`), not a plain `def`, so that the `Group`
structure Mathlib registers on `↥(Matrix.symplecticGroup ι (ZMod 2))` transfers by transparency to
`↥(binarySymplecticGroup ι)` — the inverses and `Subgroup.closure` the downstream fixed-matching
generation theorem (Theorem D.1) needs; a non-reducible `def` would hide that instance. -/
abbrev binarySymplecticGroup (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submonoid (Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) :=
  Matrix.symplecticGroup ι (ZMod 2)

omit [Fintype ι] in
/-- The paper's Gram matrix `J = [[0, I], [I, 0]]` (Eq. setup-form) **is** Mathlib's canonical
symplectic matrix `Matrix.J` over `𝔽₂`. Mathlib's `Matrix.J` is `[[0, -I], [I, 0]]`; in
characteristic two `-1 = 1`, so the anti-diagonal `-I` block equals `I` and the two agree with the
existing `CliffordCSS.symplecticMatrix = fromBlocks 0 1 1 0` (Nielsen & Chuang's `Λ`, eq. (10.84)). -/
theorem J_eq_symplecticMatrix :
    Matrix.J ι (ZMod 2) = (symplecticMatrix : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) := by
  rw [Matrix.J, symplecticMatrix, neg_eq_self_zmod2]

/-- **The Gram matrix `J = [[0, I], [I, 0]]` is itself a symplectic matrix** — the `𝔽₂` reading of
Mathlib's `SymplecticGroup.J_mem`, transported along `J_eq_symplecticMatrix`. (At width one it is
the "swap" block, the second terminal block of `Sp(2, 𝔽₂)`.) -/
theorem symplecticMatrix_mem_binarySymplecticGroup :
    (symplecticMatrix : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∈ binarySymplecticGroup ι := by
  rw [← J_eq_symplecticMatrix]
  exact SymplecticGroup.J_mem ι (ZMod 2)

/-- **Eq. setup-symplectic, first reading.** A matrix lies in the binary symplectic group iff it
preserves the form as `G J Gᵀ = J`, written in the paper's Gram matrix `J = symplecticMatrix`.
Mathlib's `SymplecticGroup.mem_iff` rephrased through `J_eq_symplecticMatrix`. -/
theorem mem_binarySymplecticGroup_iff {G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} :
    G ∈ binarySymplecticGroup ι ↔ G * symplecticMatrix * Gᵀ = symplecticMatrix := by
  unfold binarySymplecticGroup
  rw [SymplecticGroup.mem_iff, J_eq_symplecticMatrix]

/-- **Eq. setup-symplectic, second reading.** The equivalent form `Gᵀ J G = J`; the paper notes the
two readings are equivalent (because `J² = I`) but say different things in blocks. Mathlib's
`SymplecticGroup.mem_iff'` rephrased through `J_eq_symplecticMatrix`. -/
theorem mem_binarySymplecticGroup_iff' {G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} :
    G ∈ binarySymplecticGroup ι ↔ Gᵀ * symplecticMatrix * G = symplecticMatrix := by
  unfold binarySymplecticGroup
  rw [SymplecticGroup.mem_iff', J_eq_symplecticMatrix]

/-! ### The form-side membership criterion -/

/-- The twisted inner product of two `M`-transformed row vectors is the bilinear form of the
conjugate `M Λ Mᵀ`: `⟨u ᵥ* M, v ᵥ* M⟩ = u ⬝ᵥ (M Λ Mᵀ) *ᵥ v`. Pure matrix reassociation
(`Matrix.mulVec_mulVec`, `Matrix.mulVec_transpose`, `Matrix.dotProduct_mulVec`); it is what turns
"preserves the symplectic form" into the matrix identity `M Λ Mᵀ = Λ`. -/
theorem symplecticForm_vecMul_eq_dotProduct (M : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
    (u v : ι ⊕ ι → ZMod 2) :
    symplecticForm (u ᵥ* M) (v ᵥ* M) = u ⬝ᵥ (M * symplecticMatrix * Mᵀ) *ᵥ v := by
  rw [symplecticForm, ← Matrix.mulVec_transpose M v, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec u M]

/-- **The form-side membership criterion.** A matrix lies in the binary symplectic group **iff** it
preserves the symplectic form under the right row action: `M ∈ Sp(2n, 𝔽₂) ↔ ⟨u ᵥ* M, v ᵥ* M⟩ =
⟨u, v⟩` for all row vectors `u, v`.

This is the *definition-facing* reading of `Sp` — "preserves the form" — as opposed to the block
equations of `fromBlocks_mem_binarySymplecticGroup_iff`. The `mpr` direction is the natural entry
point whenever a matrix arises from an action known to preserve commutation rather than from
explicit blocks; the `mp` direction is what a consumer of an established `Sp` membership actually
wants to use, and the block readings do not provide it.

Both directions run through `symplecticForm_vecMul_eq_dotProduct`, which turns the form into
`u ⬝ᵥ (M Λ Mᵀ) *ᵥ v`: forward, rewriting by `M Λ Mᵀ = Λ` is immediate; backward,
`dotProduct_eq` (with `dotProduct_comm`) strips the left vector and `Matrix.mulVec_injective` the
right. -/
theorem mem_binarySymplecticGroup_iff_symplecticForm_vecMul
    {M : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} :
    M ∈ binarySymplecticGroup ι ↔
      ∀ u v, symplecticForm (u ᵥ* M) (v ᵥ* M) = symplecticForm u v := by
  rw [mem_binarySymplecticGroup_iff]
  constructor
  · intro hM u v
    rw [symplecticForm_vecMul_eq_dotProduct, hM, symplecticForm]
  · intro h
    refine Matrix.mulVec_injective (funext fun v => dotProduct_eq _ _ fun u => ?_)
    rw [dotProduct_comm, dotProduct_comm (symplecticMatrix *ᵥ v),
      ← symplecticForm_vecMul_eq_dotProduct, h u v, symplecticForm]

omit [DecidableEq ι] in
/-- **Convention c2, the right action** `(x | z) G = (xA + zC | xB + zD)` (Eq. setup-blocks): with
the `2n`-vector written `(x | z) = Sum.elim x z` and `G = [[A, B], [C, D]]` a block matrix, the row
vector acts from the right via `Matrix.vecMul`. Mathlib's `Matrix.vecMul_fromBlocks` presented in
the paper's polarized `(x | z)` split. -/
theorem vecMul_fromBlocks_blocks (A B C D : Matrix ι ι (ZMod 2)) (x z : ι → ZMod 2) :
    Matrix.vecMul (Sum.elim x z) (Matrix.fromBlocks A B C D)
      = Sum.elim (Matrix.vecMul x A + Matrix.vecMul z C)
          (Matrix.vecMul x B + Matrix.vecMul z D) := by
  rw [Matrix.vecMul_fromBlocks]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- **Eq. setup-blockeqs.** The block form of the symplectic condition (first reading): a block
matrix `G = [[A, B], [C, D]]` lies in `Sp(2n, 𝔽₂)` iff the two diagonal products are symmetric,
`A Bᵀ = B Aᵀ` and `C Dᵀ = D Cᵀ`, and the mixed products are complementary, `A Dᵀ + B Cᵀ = I`. The
fourth block equation `D Aᵀ + C Bᵀ = I` produced by `G J Gᵀ = J` is the transpose of the third and
so is not listed. Obtained by expanding `G J Gᵀ = J` with `Matrix.fromBlocks_multiply` /
`fromBlocks_transpose` / `fromBlocks_inj`, then reducing `X + Y = 0 ↔ X = Y` in characteristic
two. -/
theorem fromBlocks_mem_binarySymplecticGroup_iff (A B C D : Matrix ι ι (ZMod 2)) :
    Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι ↔
      A * Bᵀ = B * Aᵀ ∧ C * Dᵀ = D * Cᵀ ∧ A * Dᵀ + B * Cᵀ = 1 := by
  have hcancel : ∀ X Y : Matrix ι ι (ZMod 2), (X + Y = 0) ↔ X = Y := fun X Y => by
    rw [add_eq_zero_iff_eq_neg, neg_eq_self_zmod2]
  rw [mem_binarySymplecticGroup_iff, symplecticMatrix, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [mul_zero, mul_one, zero_add, add_zero, Matrix.fromBlocks_inj]
  rw [hcancel, hcancel]
  constructor
  · rintro ⟨h1, h2, _, h4⟩
    refine ⟨h1.symm, h4.symm, ?_⟩
    rw [add_comm]; exact h2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1.symm, ?_, ?_, h2.symm⟩
    · rw [add_comm]; exact h3
    · have := congrArg Matrix.transpose h3
      simpa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_one] using this

/-- **Eq. setup-blockeqs, second reading.** The block form of the symplectic condition read off the
equivalent `Gᵀ J G = J`: a block matrix `G = [[A, B], [C, D]]` lies in `Sp(2n, 𝔽₂)` iff `Aᵀ C` and
`Bᵀ D` are symmetric (`Aᵀ C = Cᵀ A`, `Bᵀ D = Dᵀ B`) and `Aᵀ D + Cᵀ B = I`. The companion of
`fromBlocks_mem_binarySymplecticGroup_iff`; the two together give all six relations of
Eq. (d1-sympl). It follows from the first reading by transpose-closure of the symplectic group
(`SymplecticGroup.transpose_mem_iff`): `Gᵀ = [[Aᵀ, Cᵀ], [Bᵀ, Dᵀ]]` is symplectic iff `G` is, and the
first reading applied to `Gᵀ`'s blocks is exactly the second reading of `G`'s. -/
theorem fromBlocks_mem_binarySymplecticGroup_iff' (A B C D : Matrix ι ι (ZMod 2)) :
    Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι ↔
      Aᵀ * C = Cᵀ * A ∧ Bᵀ * D = Dᵀ * B ∧ Aᵀ * D + Cᵀ * B = 1 := by
  rw [← SymplecticGroup.transpose_mem_iff, Matrix.fromBlocks_transpose,
    fromBlocks_mem_binarySymplecticGroup_iff, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.transpose_transpose]

end CliffordCSS

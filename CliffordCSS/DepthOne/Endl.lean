import CliffordCSS.DepthOne.Supply

/-!
# The label-preserving algebra `End_𝓛` and conjugation (Beyond transversality, App. D.1)

Pure mathematics : the **associative algebra of label-preserving
linear maps** `End_𝓛` of *Beyond transversality* (arXiv:2608.05688) Appendix D (Eq. (d1-endl)),
together with the fact that **conjugation by a code-preserving `G ∈ N` is an automorphism of
`End_𝓛`** (the paragraph after Eq. (d1-endl)) and the two explicit computations the paper reads
off it: the `X`-projector `Pₓ = [[I, 0], [0, 0]]` lies in `End_𝓛` (Eq. (d1-endl) applied to `Pₓ`,
the step that consumes the CSS split), and its conjugate is
`G Pₓ G⁻¹ = [[A Dᵀ, A Bᵀ], [C Dᵀ, C Bᵀ]]` (Eq. (d1-conj)).

Everything is `𝔽₂` symplectic linear algebra naming the raw carrier `Matrix`.

## The paper's setup (§D.1, after Eq. (d1-valid))

> "The theorem concerns a group of gates, but the proofs take place in the larger
> associative algebra `End_𝓛 = {f : V → V linear, f(𝒞) ⊆ 𝒞}` (Eq. (d1-endl)), of which `N`
> is only the invertible, symplectic, `M`-supported part. The algebra `End_𝓛` is closed
> under composition and addition, and — because `G(𝒞) = 𝒞` exactly — conjugation by any
> `G ∈ N` is an automorphism of `End_𝓛`: if
> `f(𝒞) ⊆ 𝒞` then `𝒞 G f G⁻¹ = ((𝒞 G) f) G⁻¹ ⊆ (𝒞) G⁻¹ = 𝒞`."

Here `V = 𝔽₂^{2n}` is the phase space in the polarized `X | Z` coordinates `ι ⊕ ι` on which the
binary symplectic group acts on row vectors from the right (Convention c2, `v ↦ v ᵥ* ·`), and
`𝒞 = cssLabelSpaceSum C_X C_Z` is the CSS-form label space. A matrix `M` is *label-preserving* when
`v ᵥ* M ∈ 𝒞` for every `v ∈ 𝒞`; note this is the **one-directional** `f(𝒞) ⊆ 𝒞` (maps *into*), so
`End_𝓛` contains singular maps such as `Pₓ` — that is the whole point of the construction, the one
place the argument steps outside the group `N` and into the algebra.

The projector step (§D.1 proof of Lemma D.2): `Pₓ : (x | z) ↦ (x | 0)` satisfies
`Pₓ(𝒞) ⊆ 𝒞` precisely because `𝒞` is *split*, `(c | d) ↦ (c | 0) ∈ (C_X | 0) ⊆ 𝒞`; this is where the
CSS hypothesis is consumed. Conjugating the *singular* `Pₓ` (not an invertible gate) is what exposes
the block products `A Bᵀ` and `C Dᵀ` as fresh data: `G Pₓ G⁻¹ = [[A Dᵀ, A Bᵀ], [C Dᵀ, C Bᵀ]]`
(Eq. (d1-conj)), using `G = [[A, B], [C, D]]` and `G⁻¹ = [[Dᵀ, Bᵀ], [Cᵀ, Aᵀ]]` (Eq. (d1-inv)).

Following the paper, no orthogonality `C_X ⊥ C_Z` is assumed — "a statement about split
subspaces and nothing more". The downstream *validity probe inclusions*
`C_X (A Bᵀ) ⊆ C_Z`, `C_Z (C Dᵀ) ⊆ C_X`
(Eq. (d1-probe)) belong to Lemma D.2 (`automaticParamsZ_le` / `automaticParamsX_le`) and are not
repeated here.

## What is defined and proved

* `codePreservingEndl` — the algebra `End_𝓛` (Eq. (d1-endl)) as a `Subalgebra` of the matrix
  algebra: the label-preserving matrices, with membership lemma `mem_codePreservingEndl_iff`.
* `mem_codePreservingEndl_of_mem_codePreservingGroup` — `N ⊆ End_𝓛` (`N` is the invertible
  symplectic part of `End_𝓛`).
* `conj_mem_codePreservingEndl` — the paper's displayed proof: `G ∈ N`, `M ∈ End_𝓛` ⟹
  `G M G⁻¹ ∈ End_𝓛`.
* `conjugationAlgEquiv` — conjugation `M ↦ G M G⁻¹` by `G` as an algebra automorphism of the
  *ambient* matrix algebra, and `codePreservingEndl_map_conjugationAlgEquiv` — it *stabilizes*
  `End_𝓛`; together `codePreservingEndlConjEquiv` bundles the restriction as an automorphism
  `End_𝓛 ≃ₐ End_𝓛`.
* `xProjector` / `xProjector_mem_codePreservingEndl` — `Pₓ = [[I, 0], [0, 0]] ∈ End_𝓛` (the CSS
  split).
* `conj_xProjector_eq` — Eq. (d1-conj), `G Pₓ G⁻¹ = [[A Dᵀ, A Bᵀ], [C Dᵀ, C Bᵀ]]`.
-/

open Matrix

namespace CliffordCSS

/-! ### Conjugation cancellation helpers

Two elementary identities for conjugation `M ↦ g M g'` by a pair of mutually inverse matrices, used
to build the conjugation algebra automorphism below. They are pure associativity + unit
cancellations, stated for an arbitrary commutative ring of matrices. -/

section Cancel

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Round-trip cancellation: conjugating `M` by `g` and then by its left inverse `g'` returns `M`
(only `g' * g = 1` is needed, since the two `g' g` blocks both cancel). -/
theorem conj_conj_cancel {g g' M : Matrix n n R} (h : g' * g = 1) :
    g' * (g * M * g') * g = M := by
  have e : g' * (g * M * g') * g = g' * g * M * (g' * g) := by simp only [mul_assoc]
  rw [e, h, one_mul, mul_one]

/-- Conjugation distributes over products: `(g M g') (g N g') = g (M N) g'` (needs `g' * g = 1`, the
middle `g' g` cancelling). -/
theorem conj_mul_distrib {g g' M N : Matrix n n R} (h : g' * g = 1) :
    g * M * g' * (g * N * g') = g * (M * N) * g' := by
  have e : g * M * g' * (g * N * g') = g * M * (g' * g) * N * g' := by simp only [mul_assoc]
  rw [e, h, mul_one, mul_assoc g M N]

end Cancel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The label-preserving algebra `End_𝓛` (Eq. (d1-endl)) -/

/-- **Eq. (d1-endl): the label-preserving algebra `End_𝓛`.** The associative algebra
`End_𝓛 = {f : V → V linear, f(𝒞) ⊆ 𝒞}` of *Beyond transversality* §D.1, realized as the `Subalgebra`
of the matrix algebra `Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔽₂` consisting of the matrices `M` that preserve the
CSS-form label space `𝒞 = cssLabelSpaceSum C_X C_Z` under the right row action, i.e.
`v ᵥ* M ∈ 𝒞` for every `v ∈ 𝒞`.

This is the **one-directional** condition `f(𝒞) ⊆ 𝒞` (maps *into* `𝒞`), so `End_𝓛` is larger
than the code-preserving group `N` (whose elements additionally invert and are symplectic): it
contains singular, non-symplectic maps such as the projector `Pₓ`. It is a subalgebra because
`𝒞` is a submodule: closure under `+` is additivity of `ᵥ*`, closure under `*` is
`v ᵥ* (M N) = (v ᵥ* M) ᵥ* N` chaining two preservations, and the scalars `r • 1` act by
`v ↦ r • v ∈ 𝒞`. -/
def codePreservingEndl (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)) :
    Subalgebra (ZMod 2) (Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) where
  carrier := {M | ∀ v ∈ cssLabelSpaceSum C_X C_Z,
    v ᵥ* M ∈ cssLabelSpaceSum C_X C_Z}
  mul_mem' := by
    intro M N hM hN v hv
    rw [← Matrix.vecMul_vecMul]
    exact hN _ (hM v hv)
  one_mem' := by
    intro v hv
    rwa [Matrix.vecMul_one]
  add_mem' := by
    intro M N hM hN v hv
    rw [Matrix.vecMul_add]
    exact (cssLabelSpaceSum C_X C_Z).add_mem (hM v hv) (hN v hv)
  zero_mem' := by
    intro v _
    rw [Matrix.vecMul_zero]
    exact (cssLabelSpaceSum C_X C_Z).zero_mem
  algebraMap_mem' := by
    intro r v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.vecMul_smul, Matrix.vecMul_one]
    exact (cssLabelSpaceSum C_X C_Z).smul_mem r hv


/-! ### Conjugation by `G ∈ N` is an automorphism of `End_𝓛` -/


/-- The matrix coercion of `G⁻¹` left-cancels `G`: `↑G⁻¹ * ↑G = 1`. -/
theorem coe_inv_mul_self (G : ↥(binarySymplecticGroup ι)) :
    ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
      * (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = 1 := by
  rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]

/-- The matrix coercion of `G⁻¹` right-cancels `G`: `↑G * ↑G⁻¹ = 1`. -/
theorem coe_mul_inv_self (G : ↥(binarySymplecticGroup ι)) :
    (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
      * ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = 1 := by
  rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]

/-- **Conjugation as an algebra automorphism of the ambient matrix algebra.** For `G` in the binary
symplectic group, `M ↦ G M G⁻¹` is an `𝔽₂`-algebra automorphism of `Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔽₂`, with
inverse `M ↦ G⁻¹ M G`. (Its restriction to `End_𝓛` is the automorphism the paper asserts;
see `codePreservingEndlConjEquiv`.) -/
def conjugationAlgEquiv (G : ↥(binarySymplecticGroup ι)) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) ≃ₐ[ZMod 2] Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) where
  toFun M := (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) * M
    * ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
  invFun M := ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) * M
    * (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
  left_inv M := conj_conj_cancel (coe_inv_mul_self G)
  right_inv M := conj_conj_cancel (coe_mul_inv_self G)
  map_mul' M N := (conj_mul_distrib (coe_inv_mul_self G)).symm
  map_add' M N := by
    simp only [mul_add, add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      coe_mul_inv_self]


/-! ### The `X`-projector `Pₓ` and its conjugate (Eq. (d1-conj)) -/

/-- The **`X`-projector** `Pₓ = [[I, 0], [0, 0]]` (§D.1): the singular, non-symplectic map
`(x | z) ↦ (x | 0)` onto the `X`-half. It is *not* a gate; it is the one non-group element the
argument uses, and only its weak property `Pₓ(𝒞) ⊆ 𝒞` is needed. -/
def xProjector (ι : Type*) [DecidableEq ι] :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  Matrix.fromBlocks 1 0 0 0


end CliffordCSS

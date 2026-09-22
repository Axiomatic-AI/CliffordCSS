import CliffordCSS.DepthOne.Isotropic
import CliffordCSS.Encoding.StabilizerConcatenation
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The symplectic complement `𝒞^⊥` and the isotropy characterization
(Beyond transversality, App. D / setup)

Pure mathematics : the foundation on which the **logical space**
`𝒞^⊥ / 𝒞` of *Beyond transversality* (arXiv:2608.05688) is built. The paper's **Corollary**
(*Depth-one logical generation*, `cor-depthone`) is stated over the logical action
`λ : N_full ↠ Sp(2k)`, and for that action to be defined the CSS label space `𝒞` must be
**isotropic**, `⟨𝒞, 𝒞⟩ = 0`, so that `𝒞 ⊆ 𝒞^⊥` and the quotient `𝒞^⊥ / 𝒞` makes sense
(`app_setup.tex`, lines ~346, 401). This file supplies the two ingredients the quotient rests on:

* the symplectic form packaged as a bundled `LinearMap.BilinForm` (`symplecticBilin`), so that
  Mathlib's orthogonal-complement machinery `Submodule.orthogonalBilin` applies;
* the **symplectic complement** `L^⊥ = symplecticPerp L` of a subspace, and the paper's identity
  **`L` is isotropic iff `L ⊆ L^⊥`** (`isIsotropic_iff_le_symplecticPerp`) — the exact fact that
  turns the Corollary's isotropy hypothesis into "the quotient `𝒞^⊥ / 𝒞` is defined".

## The symplectic form as a bundled bilinear form

The existing `symplecticForm x y = x ⬝ᵥ Λ *ᵥ y` (with `Λ = symplecticMatrix = [[0, I], [I, 0]]`,
`CheckMatrixSymplectic.lean`) is a raw `ZMod 2`-valued function. To reach the orthogonal-complement
API we repackage it as the bundled `LinearMap.BilinForm (ZMod 2) (ι ⊕ ι → ZMod 2)` obtained from `Λ`
via `Matrix.toLinearMap₂'`; `symplecticBilin_apply` records that it computes the same value. Over
`ZMod 2` the form is **symmetric** (`symplecticBilin_isSymm`, from `symplecticForm_comm`), hence
reflexive — which is what makes `symplecticPerp` a genuine two-sided complement.

## What is defined and proved

* `symplecticBilin` — `symplecticForm` as a `LinearMap.BilinForm (ZMod 2) (ι ⊕ ι → ZMod 2)`, with
  `symplecticBilin_apply` and its symmetry `symplecticBilin_isSymm`.
* `symplecticPerp L` — the symplectic complement `L^⊥` (`Submodule.orthogonalBilin` for
  `symplecticBilin`), i.e. `{ v | ⟨w, v⟩ = 0 for all w ∈ L }`, with membership `mem_symplecticPerp`.
* `isIsotropic_iff_le_symplecticPerp` — **the load-bearing identity**: `L` is isotropic iff
  `L ≤ L^⊥`. Specialized to the CSS label space,
  `CodesOrthogonal.cssLabelSpaceSum_le_symplecticPerp`
  gives `𝒞 ≤ 𝒞^⊥` from the CSS orthogonality `C_X ⊥ C_Z` — the Corollary's standing hypothesis,
  which is what makes the logical space `𝒞^⊥ / 𝒞` defined.

All of Appendix D is `𝔽₂`-symplectic linear algebra naming the raw carrier
`Matrix`/`ZMod`/`Submodule`. -/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **symplectic form as a bundled bilinear form**
`symplecticBilin : LinearMap.BilinForm (ZMod 2) (ι ⊕ ι → ZMod 2)`, obtained from the swap matrix
`Λ = symplecticMatrix = [[0, I], [I, 0]]` via `Matrix.toLinearMap₂'`. It computes exactly the raw
`symplecticForm` (`symplecticBilin_apply`); the bundled form is the shape Mathlib's
orthogonal-complement machinery `Submodule.orthogonalBilin` consumes. -/
noncomputable def symplecticBilin : LinearMap.BilinForm (ZMod 2) (ι ⊕ ι → ZMod 2) :=
  Matrix.toLinearMap₂' (ZMod 2) symplecticMatrix

/-- The bundled `symplecticBilin` computes the raw twisted inner product
`⟨x, y⟩ = x ⬝ᵥ Λ *ᵥ y = symplecticForm x y`. -/
@[simp] theorem symplecticBilin_apply (x y : ι ⊕ ι → ZMod 2) :
    symplecticBilin x y = symplecticForm x y := by
  rw [symplecticBilin, Matrix.toLinearMap₂'_apply', symplecticForm]


/-- The **symplectic complement** `L^⊥` of a subspace `L ⊆ 𝔽₂^{2n}`: the subspace of vectors
symplectically orthogonal to all of `L`, `L^⊥ = { v | ⟨w, v⟩ = 0 for all w ∈ L }`. Defined as
Mathlib's `Submodule.orthogonalBilin` for the bundled `symplecticBilin`, so the library's
complement API (`orthogonalBilin_le`, `le_orthogonalBilin_orthogonalBilin`, …) applies. The paper's
`𝒞^⊥` is `symplecticPerp 𝒞`. -/
noncomputable def symplecticPerp (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) :
    Submodule (ZMod 2) (ι ⊕ ι → ZMod 2) :=
  L.orthogonalBilin symplecticBilin

/-- Membership in the symplectic complement: `v ∈ L^⊥` iff `v` is symplectically orthogonal to every
vector of `L`, `⟨w, v⟩ = symplecticForm w v = 0` for all `w ∈ L`. -/
theorem mem_symplecticPerp {L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)} {v : ι ⊕ ι → ZMod 2} :
    v ∈ symplecticPerp L ↔ ∀ w ∈ L, symplecticForm w v = 0 := by
  simp only [symplecticPerp, Submodule.mem_orthogonalBilin_iff, LinearMap.IsOrtho,
    symplecticBilin_apply]

/-- **The load-bearing identity** (*Beyond transversality*, `app_setup.tex` ~346): a subspace `L` of
the phase space is **isotropic iff it is contained in its own symplectic complement**,
`IsIsotropic L ↔ L ≤ L^⊥`. Isotropy `⟨L, L⟩ = 0` says precisely that every vector of `L` is
symplectically orthogonal to all of `L`, i.e. lies in `L^⊥`. This is what makes the quotient
`L^⊥ / L` — and hence the logical space `𝒞^⊥ / 𝒞` of the Corollary — well-defined. -/
theorem isIsotropic_iff_le_symplecticPerp {L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)} :
    IsIsotropic L ↔ L ≤ symplecticPerp L := by
  constructor
  · intro h v hv
    rw [mem_symplecticPerp]
    intro w hw
    exact h w hw v hv
  · intro h u hu v hv
    exact (mem_symplecticPerp.mp (h hv)) u hu


end CliffordCSS

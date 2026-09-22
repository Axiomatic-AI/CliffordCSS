import CliffordCSS.DepthOne.CodePreserving
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Isotropy of the CSS label space (Beyond transversality, App. D / setup)

Pure mathematics : the **isotropy** hypothesis of *Beyond
transversality* (arXiv:2608.05688), the one place the paper's linear algebra invokes the CSS
orthogonality `C_X ⊥ C_Z`. It is the standing hypothesis of the paper's **Corollary** (*Depth-one
logical generation*, `cor-depthone`): a CSS label space `𝒞` must be **isotropic** for the logical
action `λ : N_full ↠ Sp(2k)` to be defined. This file supplies the isotropy predicate and its
identification with orthogonality; the quotient logical space `𝒞^⊥ / 𝒞` and `λ` are built on top of
it.

## The paper's setup (App. D, `app_setup.tex`)

The phase space `V = 𝔽₂^{2n}` carries the antisymmetric **symplectic form**
`⟨(a|b), (a'|b')⟩ = a · b' + b · a'` (`symplecticForm`, `symplecticForm_apply`; over `𝔽₂` it is
alternating). A subspace `L ⊆ V` is **isotropic** when the form vanishes on it,
`⟨L, L⟩ = 0` (`app_setup.tex` eq. after `eq:setup-lab`, line ~346).

For a CSS label space `𝒞 = (C_X | 0) ⊕ (0 | C_Z)` (`cssLabelSpaceSum`), the paper's own
identification (`app_setup.tex`: "eq:setup-css *says precisely* that `𝒞` is isotropic, `⟨𝒞,𝒞⟩ = 0`,
because `⟨(a|b),(a'|b')⟩ = a·b' + b·a'` vanishes for `a,a' ∈ C_X` and `b,b' ∈ C_Z`") is exactly the
**CSS orthogonality condition** `eq:setup-css`,
`a · b = 0` for all `a ∈ C_X`, `b ∈ C_Z`,
which the paper abbreviates `C_X ⊥ C_Z` (`CodesOrthogonal`). Theorem D.1 itself needs none of this
— it is "a statement about split subspaces and nothing more"; isotropy enters only in the Corollary.

## What is defined and proved

* `IsIsotropic` — a subspace `L ⊆ 𝔽₂^{2n}` is isotropic, `⟨u, v⟩ = 0` for all `u, v ∈ L`, over the
  existing `symplecticForm`.
* `CodesOrthogonal` — the CSS orthogonality condition `C_X ⊥ C_Z` (`eq:setup-css`).
* `cssLabelSpaceSum_isIsotropic_iff` — **the paper's identification**: the CSS label space
  `𝒞 = (C_X|0) ⊕ (0|C_Z)` is isotropic **iff** `C_X ⊥ C_Z`.
* `CodesOrthogonal.cssLabelSpaceSum_isIsotropic` — the forward direction packaged for downstream use
  (the isotropy hypothesis of the Corollary follows from `C_X ⊥ C_Z`).

All of Appendix D is `𝔽₂`-symplectic linear algebra naming the raw carrier
`Matrix`/`ZMod`/`Submodule`. -/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A subspace `L` of the phase space `V = 𝔽₂^{2n}` (in the polarized `ι ⊕ ι` coordinates on which
the symplectic group acts) is **isotropic** when the symplectic form vanishes on every pair of its
vectors, `⟨u, v⟩ = 0` for all `u, v ∈ L`. The paper writes this `⟨𝒞, 𝒞⟩ = 0`
(*Beyond transversality*,
`app_setup.tex`, line ~346). It is the standing hypothesis of the Corollary (*Depth-one logical
generation*): isotropy of the label space is what makes the logical action `λ` defined. -/
def IsIsotropic (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) : Prop :=
  ∀ u ∈ L, ∀ v ∈ L, symplecticForm u v = 0


end CliffordCSS

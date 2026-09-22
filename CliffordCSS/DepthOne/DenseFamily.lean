import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Perm.Basic

/-!
# The dense diagonal parameter families and their block-diagonal slices
(Beyond transversality, App. D.1 — "Relation to the dense families")

Pure mathematics : the `𝔽₂`-linear-algebra content of the §D.1
subsection *Relation to the dense families* (`sec:d1-dense`) of *Beyond transversality*
(arXiv:2608.05688). Everything here is `𝔽₂` symplectic linear algebra, and it names the raw carrier
type `Matrix` (the shear parameters `S` are symmetric
`n × n` matrices over `𝔽₂`).

## The paper's setup (§D.1)

The dense `Z`-diagonal circuits `U_Z(S) = [[I, S], [0, I]]` act on labels by
`(a | b) ↦ (a | b + aS)` and compose additively, `U_Z(S) U_Z(S') = U_Z(S + S')`. Hence the *family*
`S^Z` is canonically an
`𝔽₂`-**vector space**, "namely the space of admissible parameters `{S ∈ Sym(n) : C_X S ⊆ C_Z}`"
(where `C_X S ⊆ C_Z` means `x ᵥ* S ∈ C_Z` for every `x ∈ C_X`, `ᵥ*` the row-vector action of
Convention c2). We formalize this vector space directly as `admissibleParams`; a genuine
`Submodule` of the `𝔽₂`-space of matrices *is* the "canonically an `𝔽₂`-vector space" claim.

A **matching** `M` of the `n` qubits is an involution `σ` of the qubits (Convention c3): its cells
are the pairs `{i, σ i}` (`σ i ≠ i`) and the singletons `{i}` (`σ i = i`). A matrix is
`M`-**block-diagonal** (`IsCellDiagonal σ`) when its `(i, j)` entry vanishes off the cells, i.e.
whenever `j ∉ {i, σ i}`. For the shear `U_Z(S)` (whose blocks are `A = D = I`, `C = 0`, `B = S`)
being `M`-block-diagonal is exactly `S` being `M`-block-diagonal, so `S^Z_M`, the `M`-block-diagonal
part of `S^Z`, is `admissibleParamsBlockDiag = admissibleParams ⊓ cellDiagonalMatrices`.

## What is proved

* `admissibleParams C_dom C_cod` — the admissible-parameter space `{S : Sᵀ = S ∧ C_dom S ⊆ C_cod}`
  as a `Submodule` over `𝔽₂` (the "canonically an `𝔽₂`-vector space" claim). The paper's named
  families are the two instantiations `admissibleZParams C_X C_Z = admissibleParams C_X C_Z` (`S^Z`)
  and `admissibleXParams C_X C_Z = admissibleParams C_Z C_X` (`S^X`, dually with `C_Z T ⊆ C_X`).
* `cellDiagonalMatrices σ` — the `M`-block-diagonal matrices as a `Submodule`.
* `admissibleParamsBlockDiag_le` — `S^Z_M ≤ S^Z`: the `M`-block-diagonal part of an admissible
  family is a subspace of it (the parameter reading of Eq. (D-slice) `S^Z_M = S^Z ∩ Sp(2n)_M`).
* `iSup_admissibleParamsBlockDiag_le` — **Eq. (D-span), inclusion direction**
  `span ⋃_M S^Z_M ⊆ S^Z` (in Lean `⨆_M S^Z_M ≤ S^Z`; the `Submodule` supremum `⨆` **is**
  `Submodule.span` of the union, `Submodule.iSup_eq_span`). This is a **generic lattice fact**
  (`⨆ i, (p ⊓ q i) ≤ p`, i.e. `iSup_le ∘ inf_le_left`) carrying no dense-family content: it holds
  verbatim with `admissibleParams` replaced by an arbitrary submodule and `cellDiagonalMatrices` by
  an arbitrary family. The paper's substantive claim about Eq. (D-span) — that the inclusion is
  *strict in general* (Eq. (D-dims)) — is a numeric rank computation deliberately out of scope.
  Instantiate at `C_X C_Z` for `S^Z` and at `C_Z C_X` for `S^X`.

## Deliberately deferred

The paper's Eq. (D-dims) — that Eq. (D-span) is *strict in general*, witnessed on the doubly-even
self-dual `[[6,2,2]]` code by the computed dimensions `dim S^Z_M = 4`, `dim S^Z = 14`,
`dim (span ⋃_M S^Z_M) = 13` — is a numeric claim about a specific `n = 6` code. Certifying it needs
a rank computation over the `2²¹` symmetric `𝔽₂` matrices in `Sym(6)`, infeasible for the kernel's
`decide` and off-limits to `native_decide` (numerics policy). It is honest tracked debt
(`descoped:numeric-intractable` in the plan), separate from the structural inclusion Eq. (D-span),
which is proved outright here.
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι]

/-- The **admissible-parameter space** `{S : Sᵀ = S ∧ C_dom S ⊆ C_cod}` of *Beyond transversality*
(§D.1), as a `Submodule` over `𝔽₂ = ZMod 2` of the symmetric `n × n` matrices sending the code
`C_dom` into `C_cod` under the row-vector action `x ↦ x ᵥ* S` (Convention c2). Because the dense
`Z`-diagonal circuits compose additively (`U_Z(S) U_Z(S') = U_Z(S + S')`), this submodule **is** the
paper's "family `S^Z` as an `𝔽₂`-vector space": its addition matches circuit composition.

The two families of §D.1 are the two instantiations: the `Z`-diagonal
`S^Z = admissibleZParams C_X C_Z` (constraint `C_X S ⊆ C_Z`) and the `X`-diagonal
`S^X = admissibleXParams C_X C_Z` (constraint `C_Z T ⊆ C_X`). No orthogonality `C_X ⊥ C_Z` is
assumed — this is "a statement about split subspaces and nothing more". -/
def admissibleParams (C_dom C_cod : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule (ZMod 2) (Matrix ι ι (ZMod 2)) where
  carrier := {S | S.IsSymm ∧ ∀ x ∈ C_dom, Matrix.vecMul x S ∈ C_cod}
  add_mem' := by
    rintro S T ⟨hSsymm, hS⟩ ⟨hTsymm, hT⟩
    refine ⟨hSsymm.add hTsymm, fun x hx => ?_⟩
    rw [Matrix.vecMul_add]
    exact C_cod.add_mem (hS x hx) (hT x hx)
  zero_mem' := by
    refine ⟨Matrix.isSymm_zero, fun x _ => ?_⟩
    rw [Matrix.vecMul_zero]
    exact C_cod.zero_mem
  smul_mem' := by
    rintro c S ⟨hSsymm, hS⟩
    refine ⟨hSsymm.smul c, fun x hx => ?_⟩
    rw [Matrix.vecMul_smul]
    exact C_cod.smul_mem c (hS x hx)

/-- Membership in the admissible-parameter space: `S ∈ admissibleParams C_dom C_cod` iff `S` is
symmetric and maps `C_dom` into `C_cod` (`x ᵥ* S ∈ C_cod` for all `x ∈ C_dom`). -/
theorem mem_admissibleParams {C_dom C_cod : Submodule (ZMod 2) (ι → ZMod 2)}
    {S : Matrix ι ι (ZMod 2)} :
    S ∈ admissibleParams C_dom C_cod ↔ S.IsSymm ∧ ∀ x ∈ C_dom, Matrix.vecMul x S ∈ C_cod :=
  Iff.rfl

/-- A matrix `S` is `M`-**block-diagonal** for the matching (involution) `σ` (§D.1) when its
`(i, j)` entry vanishes off the cells of `M`: `S i j = 0` whenever `j` lies in neither `{i}` nor the
partner `{σ i}` — i.e. `j ∉ {i, σ i}`, the cell of `i`. For an unmatched `i` (`σ i = i`) only the
diagonal entry `S i i` may be nonzero; for a matched pair only the `2 × 2` block on `{i, σ i}`. -/
def IsCellDiagonal (σ : Equiv.Perm ι) (S : Matrix ι ι (ZMod 2)) : Prop :=
  ∀ i j, j ≠ i → j ≠ σ i → S i j = 0

/-- The `M`-**block-diagonal matrices** for the matching (involution) `σ`, as a `Submodule` over
`𝔽₂`: the vanishing-off-cells condition `IsCellDiagonal σ` is closed under addition, zero and scalar
multiplication (it is an entrywise "equals `0`" constraint). -/
def cellDiagonalMatrices (σ : Equiv.Perm ι) : Submodule (ZMod 2) (Matrix ι ι (ZMod 2)) where
  carrier := {S | IsCellDiagonal σ S}
  add_mem' := by
    rintro S T hS hT i j hji hjσ
    simp only [Matrix.add_apply, hS i j hji hjσ, hT i j hji hjσ, add_zero]
  zero_mem' := by
    intro i j _ _
    simp only [Matrix.zero_apply]
  smul_mem' := by
    rintro c S hS i j hji hjσ
    simp only [Matrix.smul_apply, hS i j hji hjσ, smul_zero]

omit [Fintype ι] in
/-- Membership in the block-diagonal matrices: `S ∈ cellDiagonalMatrices σ` iff `S` is
`M`-block-diagonal (`IsCellDiagonal σ S`). -/
theorem mem_cellDiagonalMatrices {σ : Equiv.Perm ι} {S : Matrix ι ι (ZMod 2)} :
    S ∈ cellDiagonalMatrices σ ↔ IsCellDiagonal σ S :=
  Iff.rfl

/-- The `M`-**block-diagonal part** `S^Z_M` of an admissible family (§D.1): the admissible
parameters that are in addition `M`-block-diagonal, i.e. the intersection
`admissibleParams C_dom C_cod ⊓ cellDiagonalMatrices σ`. For the shear `U_Z(S)` — whose blocks are
`A = D = I`, `C = 0`, `B = S` — being `M`-block-diagonal as a symplectic matrix is exactly `S` being
`M`-block-diagonal, so this is the parameter reading of Eq. (D-slice) `S^Z_M = S^Z ∩ Sp(2n)_M`. -/
def admissibleParamsBlockDiag (C_dom C_cod : Submodule (ZMod 2) (ι → ZMod 2))
    (σ : Equiv.Perm ι) : Submodule (ZMod 2) (Matrix ι ι (ZMod 2)) :=
  admissibleParams C_dom C_cod ⊓ cellDiagonalMatrices σ

/-- **Eq. (D-slice), parameter level.** The `M`-block-diagonal part `S^Z_M` of an admissible family
is a subspace of the dense family `S^Z`: `admissibleParamsBlockDiag C_dom C_cod σ ≤
admissibleParams C_dom C_cod`. -/
theorem admissibleParamsBlockDiag_le (C_dom C_cod : Submodule (ZMod 2) (ι → ZMod 2))
    (σ : Equiv.Perm ι) :
    admissibleParamsBlockDiag C_dom C_cod σ ≤ admissibleParams C_dom C_cod :=
  inf_le_left

/-- Membership in the block-diagonal part: `S ∈ admissibleParamsBlockDiag C_dom C_cod σ` iff `S` is
symmetric, maps `C_dom` into `C_cod`, and is `M`-block-diagonal. -/
theorem mem_admissibleParamsBlockDiag {C_dom C_cod : Submodule (ZMod 2) (ι → ZMod 2)}
    {σ : Equiv.Perm ι} {S : Matrix ι ι (ZMod 2)} :
    S ∈ admissibleParamsBlockDiag C_dom C_cod σ ↔
      S.IsSymm ∧ (∀ x ∈ C_dom, Matrix.vecMul x S ∈ C_cod) ∧ IsCellDiagonal σ S := by
  rw [admissibleParamsBlockDiag, Submodule.mem_inf, mem_admissibleParams, mem_cellDiagonalMatrices]
  tauto

/-- **Eq. (D-span), inclusion direction** `span ⋃_M S^Z_M ⊆ S^Z`. The `𝔽₂`-span of the union of the
block-diagonal parts `S^Z_M`, taken over *all* matchings `M` (involutions `σ`) of the `n` qubits, is
contained in the dense family `S^Z`. In Lean the `Submodule` supremum `⨆` **is** `Submodule.span` of
the union (`Submodule.iSup_eq_span`), so `⨆_M S^Z_M ≤ S^Z` is exactly the paper's
`span ⋃_M S^Z_M ⊆ S^Z`; the `iSup` form is used because it is the canonical rendering of a submodule
join.

This inclusion is a **generic lattice fact carrying no dense-family content**. Its proof is
`iSup_le fun σ => admissibleParamsBlockDiag_le …`, i.e. the general `⨆ i, (p ⊓ q i) ≤ p`
(`iSup_le ∘ inf_le_left`): it uses nothing about symmetry, matchings, validity, or the CSS
constraint, and holds verbatim with `admissibleParams` replaced by an arbitrary submodule and
`cellDiagonalMatrices` by an arbitrary family. The paper's **substantive** claim about Eq. (D-span)
is that the inclusion is **strict in general** (Eq. (D-dims): `dim S^Z_M = 4`, `dim S^Z = 14`,
`dim (span ⋃_M S^Z_M) = 13` on the `[[6,2,2]]` code) — a numeric rank computation over `Sym(6)`,
deliberately out of scope (`descoped:numeric-intractable`). Nothing here claims that strictness. -/
theorem iSup_admissibleParamsBlockDiag_le (C_dom C_cod : Submodule (ZMod 2) (ι → ZMod 2)) :
    ⨆ σ : {σ : Equiv.Perm ι // Function.Involutive σ},
        admissibleParamsBlockDiag C_dom C_cod σ.1
      ≤ admissibleParams C_dom C_cod :=
  iSup_le fun σ => admissibleParamsBlockDiag_le C_dom C_cod σ.1

/-- The paper's **`Z`-diagonal family** `S^Z = {S ∈ Sym(n) : C_X S ⊆ C_Z}` (§D.1) as an
`𝔽₂`-vector space: `admissibleParams C_X C_Z`. -/
abbrev admissibleZParams (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule (ZMod 2) (Matrix ι ι (ZMod 2)) :=
  admissibleParams C_X C_Z

/-- The paper's **`X`-diagonal family** `S^X = {T ∈ Sym(n) : C_Z T ⊆ C_X}` (§D.1), the dual of `S^Z`
with the codes swapped: `admissibleParams C_Z C_X`. -/
abbrev admissibleXParams (C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule (ZMod 2) (Matrix ι ι (ZMod 2)) :=
  admissibleParams C_Z C_X

end CliffordCSS

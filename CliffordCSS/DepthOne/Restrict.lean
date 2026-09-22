import CliffordCSS.DepthOne.BlockDiagonal

/-!
# Restriction of a layer to a cell (Beyond transversality, App. D.1 — Lemma (Restriction))

Pure mathematics : the **Restriction lemma** of §D.1 of *Beyond
transversality* (arXiv:2608.05688) — `𝔽₂` symplectic linear algebra over the raw carrier
`Matrix`.

For a layer `G = [[A, B], [C, D]]` with `M`-block-diagonal blocks (`IsCellDiagonal σ`), the
parameter formulas (Eq. (d1-eps)) are `S^Z(G, ε) = ε₁·A Bᵀ + ε₂·Dᵀ B + ε₃·(B + Bᵀ)` (`spzParam`)
and `S^X(G, ε) = ε₁·C Dᵀ + ε₂·Cᵀ A + ε₃·(C + Cᵀ)` (`spxParam`), with `ε ∈ 𝔽₂³`; their `ε`-ranges
are the spans `Θ^Z(G) = span {A Bᵀ, Dᵀ B, B + Bᵀ}`, `Θ^X(G) = span {C Dᵀ, Cᵀ A, C + Cᵀ}` of
Lemma D.2 (`BeyondTransversalityAutoParams`). A **cell** is `{i, σ i}` (`cellFinset σ i`) and
**restriction** `(·)_b` (`restrictToCell b`) is the `b × b` submatrix; the cell block `g_b` has
blocks `X_b := restrictToCell b X`, so `S^Z(g_b, ε) = spzParam A_b B_b D_b ε`, and Eq. (d1-restrict)
`S^Z(G, ε)_b = S^Z(g_b, ε)` is exactly "`restrictToCell b` commutes with `spzParam`".

Alongside the restriction identities the file records the elementary facts every consumer of
`restrictToCell` needs: `restrictToCell_one` (`I_b = I`), `eq_zero_of_forall_restrictToCell_eq_zero`
(an `M`-block-diagonal matrix vanishing on every cell vanishes — the converse assembly direction),
and `spzParam_mem_span` / `spxParam_mem_span` (a parameter lies in the manufactured span of
Lemma D.2 it is built from).

The statements are proved for an arbitrary **`σ`-closed** finset `b` (`∀ a ∈ b, σ a ∈ b`) — a
faithful reformulation of "cell", since cells are exactly the `σ`-closed sets of size `≤ 2`
(`cellFinset_sigma_closed`).

**The crux.** `restrictToCell b` is an **algebra map on the `M`-block-diagonal matrices**:
`𝔽₂`-linear and transpose-commuting for free (submatrix facts), and *multiplicative* on a `σ`-closed
cell whenever the **left** factor is `M`-block-diagonal (`restrictToCell_mul_of_cellDiagonal`) — a
cell-diagonal row is supported on its own cell, contained in `b`, so the inner-product sum collapses
to the sum
over `b`. As only the *left* multiplicand need be block-diagonal, the `Z`-identity uses only `A, D`
(left factors of `A Bᵀ`, `Dᵀ B`) and the `X`-identity only `C` (left factor of `C Dᵀ` and, as `Cᵀ`,
of `Cᵀ A`): more general than requiring the whole layer block-diagonal, which every `G ∈ N_M`
satisfies. This is the paper's own proof ("products and sums of `M`-block-diagonal blocks are too …
restriction is multiplicative and additive on those blocks … and `𝔽₂`-linear"); no orthogonality
`C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more".
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*}

/-! ### Cells of the matching -/

section Cells
variable [DecidableEq ι]

/-- The **cell** `{i, σ i}` of qubit `i` under the matching (involution) `σ`, as a finset: the pair
`{i, σ i}` when `i` is matched (`σ i ≠ i`) and the singleton `{i}` when `i` is unmatched
(`σ i = i`). This is the raw-carrier  counterpart of `Matching.cell`. -/
def cellFinset (σ : Equiv.Perm ι) (i : ι) : Finset ι := {i, σ i}

@[simp] theorem mem_cellFinset {σ : Equiv.Perm ι} {i j : ι} :
    j ∈ cellFinset σ i ↔ j = i ∨ j = σ i := by
  simp only [cellFinset, Finset.mem_insert, Finset.mem_singleton]

/-- Every qubit lies in its own cell. -/
theorem self_mem_cellFinset (σ : Equiv.Perm ι) (i : ι) : i ∈ cellFinset σ i :=
  mem_cellFinset.mpr (Or.inl rfl)

/-- A cell is **closed under the matching**: if `a ∈ {i, σ i}` then `σ a ∈ {i, σ i}` (using
involutivity `σ² = id`). This is the property that makes restriction to a cell multiplicative on the
`M`-block-diagonal matrices. -/
theorem cellFinset_sigma_closed {σ : Equiv.Perm ι} (hσ : Function.Involutive σ) (i : ι) :
    ∀ a ∈ cellFinset σ i, σ a ∈ cellFinset σ i := by
  intro a ha
  rcases mem_cellFinset.mp ha with rfl | rfl
  · exact mem_cellFinset.mpr (Or.inr rfl)
  · exact mem_cellFinset.mpr (Or.inl (hσ i))

end Cells

/-! ### Restriction of a matrix to a cell -/

/-- **Restriction to a cell** `b` (a finset of qubits): the `b × b` submatrix
`S.submatrix Subtype.val Subtype.val`, the paper's `(·)_b`. For a cell `b = {i, σ i}` this picks out
the `w × w` block on the cell's coordinates (`w = #b ∈ {1, 2}`). -/
def restrictToCell (b : Finset ι) (S : Matrix ι ι (ZMod 2)) : Matrix b b (ZMod 2) :=
  S.submatrix Subtype.val Subtype.val

@[simp] theorem restrictToCell_apply (b : Finset ι) (S : Matrix ι ι (ZMod 2)) (i j : b) :
    restrictToCell b S i j = S i j := rfl

/-- Restriction to a cell is **additive**. -/
theorem restrictToCell_add (b : Finset ι) (S T : Matrix ι ι (ZMod 2)) :
    restrictToCell b (S + T) = restrictToCell b S + restrictToCell b T := by
  ext i j; simp [restrictToCell]

/-- Restriction to a cell **commutes with scalar multiplication** (`𝔽₂`-linearity). -/
theorem restrictToCell_smul (b : Finset ι) (c : ZMod 2) (S : Matrix ι ι (ZMod 2)) :
    restrictToCell b (c • S) = c • restrictToCell b S := by
  ext i j; simp [restrictToCell]

/-- Restriction to a cell sends `0` to `0`. -/
@[simp] theorem restrictToCell_zero (b : Finset ι) :
    restrictToCell b (0 : Matrix ι ι (ZMod 2)) = 0 := by
  ext i j; simp [restrictToCell]

/-- **Restriction preserves the identity matrix**: the `b × b` submatrix of `I` along the injection
`b ↪ ι` is `I`. -/
@[simp] theorem restrictToCell_one [DecidableEq ι] (b : Finset ι) :
    restrictToCell b (1 : Matrix ι ι (ZMod 2)) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [restrictToCell_apply, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [restrictToCell_apply, Matrix.one_apply_ne fun hv => h (Subtype.ext hv),
      Matrix.one_apply_ne h]

/-- Restriction to a cell **commutes with transpose**: `(Sᵀ)_b = (S_b)ᵀ`. -/
theorem restrictToCell_transpose (b : Finset ι) (S : Matrix ι ι (ZMod 2)) :
    restrictToCell b Sᵀ = (restrictToCell b S)ᵀ :=
  (Matrix.transpose_submatrix S _ _).symm

/-- Restriction to a cell as an `𝔽₂`-**linear map** (packaging `restrictToCell_add` /
`restrictToCell_smul`), for taking images of the manufactured spans `Θ^Z(G)`, `Θ^X(G)`. -/
def restrictToCellₗ (b : Finset ι) :
    Matrix ι ι (ZMod 2) →ₗ[ZMod 2] Matrix b b (ZMod 2) where
  toFun := restrictToCell b
  map_add' := restrictToCell_add b
  map_smul' := restrictToCell_smul b

@[simp] theorem restrictToCellₗ_apply (b : Finset ι) (S : Matrix ι ι (ZMod 2)) :
    restrictToCellₗ b S = restrictToCell b S := rfl

/-- **An `M`-block-diagonal matrix vanishing on every cell vanishes.** Off the cells the entries are
`0` by block-diagonality; on a cell they are entries of that cell's restriction. This is the
converse direction of Eq. (d1-restrict) used to assemble a blockwise conclusion into a global
one. -/
theorem eq_zero_of_forall_restrictToCell_eq_zero [DecidableEq ι] {σ : Equiv.Perm ι}
    {S : Matrix ι ι (ZMod 2)} (hS : IsCellDiagonal σ S)
    (h : ∀ i, restrictToCell (cellFinset σ i) S = 0) : S = 0 := by
  ext i j
  by_cases hji : j = i
  · subst hji
    have := congrFun (congrFun (h j) ⟨j, self_mem_cellFinset σ j⟩) ⟨j, self_mem_cellFinset σ j⟩
    simpa [restrictToCell] using this
  by_cases hjσ : j = σ i
  · subst hjσ
    have := congrFun (congrFun (h i) ⟨i, self_mem_cellFinset σ i⟩)
      ⟨σ i, mem_cellFinset.mpr (Or.inr rfl)⟩
    simpa [restrictToCell] using this
  · rw [hS i j hji hjσ, Matrix.zero_apply]

section
variable [Fintype ι]

/-- **The multiplicative crux (Eq. (d1-restrict3)).** On a `σ`-closed cell `b`, restriction is
*multiplicative* as soon as the **left** factor is `M`-block-diagonal: `(S T)_b = S_b T_b`. In the
inner product `(S T) i j = ∑ₖ S i k · T k j` with `i ∈ b`, a cell-diagonal `S` has row `i` supported
on the cell of `i`, contained in `b` (`i ∈ b` and `σ i ∈ b`); every `k ∉ b` therefore contributes
`S i k = 0`, so the full sum over the qubits collapses to the sum over `b`, i.e. `(S_b T_b) i j`.
Only the left factor need be block-diagonal; `T` is arbitrary. -/
theorem restrictToCell_mul_of_cellDiagonal {σ : Equiv.Perm ι} {b : Finset ι}
    (hb : ∀ a ∈ b, σ a ∈ b) {S T : Matrix ι ι (ZMod 2)} (hS : IsCellDiagonal σ S) :
    restrictToCell b (S * T) = restrictToCell b S * restrictToCell b T := by
  ext a c
  simp only [restrictToCell, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Finset.sum_coe_sort b (fun k => S a.1 k * T k c.1)]
  refine (Finset.sum_subset (Finset.subset_univ b) ?_).symm
  intro k _ hkb
  have hne1 : k ≠ a.1 := fun h => hkb (h ▸ a.2)
  have hne2 : k ≠ σ a.1 := fun h => hkb (h ▸ hb a.1 a.2)
  rw [hS a.1 k hne1 hne2, zero_mul]

/-! ### The parameter formulas `S^Z(G, ε)`, `S^X(G, ε)` (Eq. (d1-eps)) -/

/-- The **`Z`-parameter formula** `S^Z(G, ε) = ε₁·A Bᵀ + ε₂·Dᵀ B + ε₃·(B + Bᵀ)` (Eq. (d1-eps)) of a
layer `G = [[A, B], [C, D]]`, as a function of the three blocks it uses (`A`, `B`, `D`) and a
coefficient vector `ε ∈ 𝔽₂³`. As `ε` ranges over `𝔽₂³` its values are exactly the span
`Θ^Z(G) = span {A Bᵀ, Dᵀ B, B + Bᵀ}` of Lemma D.2. -/
def spzParam (A B D : Matrix ι ι (ZMod 2)) (ε : Fin 3 → ZMod 2) : Matrix ι ι (ZMod 2) :=
  ε 0 • (A * Bᵀ) + ε 1 • (Dᵀ * B) + ε 2 • (B + Bᵀ)

/-- The **`X`-parameter formula** `S^X(G, ε) = ε₁·C Dᵀ + ε₂·Cᵀ A + ε₃·(C + Cᵀ)` (Eq. (d1-eps)) — the
`X ↔ Z` dual of `spzParam`, using the blocks `C`, `D`, `A`. Its values over `ε ∈ 𝔽₂³` are the span
`Θ^X(G) = span {C Dᵀ, Cᵀ A, C + Cᵀ}`. -/
def spxParam (A C D : Matrix ι ι (ZMod 2)) (ε : Fin 3 → ZMod 2) : Matrix ι ι (ZMod 2) :=
  ε 0 • (C * Dᵀ) + ε 1 • (Cᵀ * A) + ε 2 • (C + Cᵀ)

/-- **The `Z`-parameters are the manufactured span of Lemma D.2**: `S^Z(G, ε)` is the
`ε`-combination of the three generators `A Bᵀ`, `Dᵀ B`, `B + Bᵀ`, hence lies in their span — which
is what makes the induced circuit `U_Z(S^Z(G, ε))` a valid `M`-supported gate for `G ∈ N_M`. -/
theorem spzParam_mem_span (A B D : Matrix ι ι (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    spzParam A B D ε ∈ Submodule.span (ZMod 2) {A * Bᵀ, Dᵀ * B, B + Bᵀ} := by
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- **The `X`-parameters are the manufactured span of Lemma D.2** (dual to `spzParam_mem_span`):
`S^X(G, ε) ∈ span {C Dᵀ, Cᵀ A, C + Cᵀ}`. -/
theorem spxParam_mem_span (A C D : Matrix ι ι (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    spxParam A C D ε ∈ Submodule.span (ZMod 2) {C * Dᵀ, Cᵀ * A, C + Cᵀ} := by
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-! ### Eq. (d1-restrict): restriction commutes with the parameter formulas -/

/-- **Eq. (d1-restrict), the `Z` side.** For a `σ`-closed cell `b` and blocks `A, D` that are
`M`-block-diagonal (`IsCellDiagonal σ`; the left factors of the two products in `S^Z`), restriction
commutes with the `Z`-parameter formula: `S^Z(G, ε)_b = S^Z(g_b, ε)`, i.e.
`restrictToCell b (spzParam A B D ε) = spzParam A_b B_b D_b ε`. Each generator restricts to its
local counterpart — `(A Bᵀ)_b = A_b B_bᵀ`, `(Dᵀ B)_b = D_bᵀ B_b`, `(B + Bᵀ)_b = B_b + B_bᵀ` — and
restriction is `𝔽₂`-linear, so it commutes with the `ε`-combination. (`B` need not be
block-diagonal: it occurs only transposed or summed, never as a left multiplicand.) -/
theorem restrictToCell_spzParam {σ : Equiv.Perm ι} (hσ : Function.Involutive σ) {b : Finset ι}
    (hb : ∀ a ∈ b, σ a ∈ b) {A B D : Matrix ι ι (ZMod 2)}
    (hA : IsCellDiagonal σ A) (hD : IsCellDiagonal σ D) (ε : Fin 3 → ZMod 2) :
    restrictToCell b (spzParam A B D ε)
      = spzParam (restrictToCell b A) (restrictToCell b B) (restrictToCell b D) ε := by
  simp only [spzParam, restrictToCell_add, restrictToCell_smul,
    restrictToCell_mul_of_cellDiagonal hb hA,
    restrictToCell_mul_of_cellDiagonal hb (isCellDiagonal_transpose hσ hD),
    restrictToCell_transpose]

/-- **Eq. (d1-restrict), the `X` side** (dual to `restrictToCell_spzParam`). For a `σ`-closed cell
`b` and a block `C` that is `M`-block-diagonal (the left factor of `C Dᵀ` and, transposed, of
`Cᵀ A`), `S^X(G, ε)_b = S^X(g_b, ε)`, i.e.
`restrictToCell b (spxParam A C D ε) = spxParam A_b C_b D_b ε`. The generators restrict as
`(C Dᵀ)_b = C_b D_bᵀ`, `(Cᵀ A)_b = C_bᵀ A_b`, `(C + Cᵀ)_b = C_b + C_bᵀ`. (`A`, `D` need not be
block-diagonal: they occur only as right multiplicands.) -/
theorem restrictToCell_spxParam {σ : Equiv.Perm ι} (hσ : Function.Involutive σ) {b : Finset ι}
    (hb : ∀ a ∈ b, σ a ∈ b) {A C D : Matrix ι ι (ZMod 2)}
    (hC : IsCellDiagonal σ C) (ε : Fin 3 → ZMod 2) :
    restrictToCell b (spxParam A C D ε)
      = spxParam (restrictToCell b A) (restrictToCell b C) (restrictToCell b D) ε := by
  simp only [spxParam, restrictToCell_add, restrictToCell_smul,
    restrictToCell_mul_of_cellDiagonal hb hC,
    restrictToCell_mul_of_cellDiagonal hb (isCellDiagonal_transpose hσ hC),
    restrictToCell_transpose]

/-! ### Every local move lifts to a global move (the "Hence …" of the lemma)

The paper's payoff: "every move available at `g_b` is the restriction of a move on `G`, obtained by
re-evaluating the same `ε` on the whole layer". A *move* is a **nonzero** parameter. Restriction
sends `0` to `0`, so a global zero parameter restricts to a zero local parameter; contrapositive, a
nonzero local parameter `S^Z(g_b, ε)` is the restriction of the nonzero global parameter `S^Z(G, ε)`
from the *same* `ε` (Eq. (d1-restrict)). -/


/-! ### Restriction carries the manufactured spans onto their local counterparts

The "Hence restriction carries `Θ^Z(G)` onto `Θ^Z(g_b)`" clause, stated via the restriction linear
map and `Submodule.map`. -/


end

end CliffordCSS

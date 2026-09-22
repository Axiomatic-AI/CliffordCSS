import CliffordCSS.Symplectic.Group
import CliffordCSS.DepthOne.DenseFamily
import CliffordCSS.DepthOne.ShearLevi

/-!
# The `M`-block-diagonal symplectic subgroup `Sp(2n)_M = 𝒟_M`
(Beyond transversality, App. D.1 — the two-fold transversal setting)

Pure mathematics : the `𝔽₂`-linear-algebra object `𝒟_M` of §D.1 of
*Beyond transversality* (arXiv:2608.05688) — the **`M`-block-diagonal symplectic matrices** for a
matching `M`. Everything here is `𝔽₂` symplectic linear algebra over the raw carrier type
`Matrix` (`2n × 2n` symplectic matrices), following the paper's Convention c4.

## The paper's setup (§D.1, Convention c4)

> "Let `𝒟_M` be the subgroup of `Sp(2n)` consisting of the `M`-block-diagonal matrices. These are
> the matrices carrying an arbitrary `Sp(4)` block on each matched pair and an arbitrary `Sp(2)`
> block on each unmatched singleton. Concretely, in the `X̂|Ẑ` convention, `g ∈ 𝒟_M` means that each
> of the four blocks `A, B, C, D` is block-diagonal for the cells of `M`."

A matching `M` is an involution `σ` of the `n` qubits (Convention c3): its **cells** are the pairs
`{i, σ i}` (`σ i ≠ i`) and singletons `{i}` (`σ i = i`). Two qubits are in the same cell iff
`j = i ∨ j = σ i`; this is an equivalence relation (using `σ² = id`). An `n × n` matrix is
`M`-block-diagonal exactly when its entries vanish across cells — the reusable predicate
`IsCellDiagonal σ` of the dense-family development (`BeyondTransversalityDenseFamily`).

We lift this to the `2n = |ι ⊕ ι|` phase-space coordinates. Writing `coordQubit := Sum.elim id id`
for the qubit a coordinate `p ∈ ι ⊕ ι` sits on (both the `X`-copy `inl i` and the `Z`-copy `inr i`
belong to qubit `i`), a symplectic matrix `G` is `M`-**block-diagonal** (`IsSpBlockDiagonal σ G`)
when `G p q = 0` whenever the qubits of `p` and `q` lie in different cells. This is the "reorder the
coordinates so each qubit's `X, Z` sit together, then `G` is block-diagonal with one `Sp(4)` block
per matched pair and one `Sp(2)` block per singleton" reading of §D.1; the `X̂|Ẑ`-block reading
"each of `A, B, C, D` is `IsCellDiagonal σ`" is `isSpBlockDiagonal_fromBlocks_iff`.

## What is proved

* `IsSpBlockDiagonal σ G` — `G` is `M`-block-diagonal (entries vanish across cells).
* `isSpBlockDiagonal_fromBlocks_iff` — Convention c4's block reading: `[[A,B],[C,D]]` is
  `M`-block-diagonal iff each of `A, B, C, D` is `IsCellDiagonal σ`.
* `isSpBlockDiagonal_one` / `isSpBlockDiagonal_mul` / `isSpBlockDiagonal_transpose` /
  `isSpBlockDiagonal_symplecticMatrix` — closure facts. The product closure uses `σ`'s involutivity
  (the cell relation is an equivalence); the Gram matrix `J = symplecticMatrix` is block-diagonal
  for *every* matching (it only links same-qubit coordinates).
* `blockDiagonalSymplecticGroup σ hσ` — `𝒟_M`, the object of study, as a genuine
  `Subgroup` of the binary symplectic group `Sp(2n, 𝔽₂)`. Closure under inverse uses the `𝔽₂`
  symplectic inverse `G⁻¹ = J Gᵀ J` (`SymplecticGroup.coe_inv`, `-J = J` in characteristic two).
* `mem_blockDiagonalSymplecticGroup_iff` / `mem_blockDiagonalSymplecticGroup_fromBlocks_iff` — the
  membership characterizations, the second being Convention c4's `g ∈ 𝒟_M ⟺` (symplectic and) each
  of `A, B, C, D` block-diagonal.
* `shearZ_isSpBlockDiagonal` / `shearX_isSpBlockDiagonal` — the shear generators `U_Z(B)`, `L_X(C)`
  are `M`-block-diagonal iff their parameter is (`IsCellDiagonal σ`); reused wherever a shear enters
  a block-diagonal product (the assembly word, the terminal factorization).

The per-cell `Sp(4)` / `Sp(2)` symplectic restriction is downstream structural content (Lemma D.5
and the reduction lemmas), not part of this definition. No orthogonality `C_X ⊥ C_Z` is used — this
is "a statement about split subspaces and nothing more".
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **qubit** a phase-space coordinate `p ∈ ι ⊕ ι` belongs to: both the `X`-copy `inl i` and the
`Z`-copy `inr i` of qubit `i` map to `i`. In the polarized `X̂ | Ẑ` split of `V = 𝔽₂^{2n}` this is
the map forgetting the `X`/`Z` polarization and keeping the qubit index. -/
def coordQubit (p : ι ⊕ ι) : ι := Sum.elim id id p

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coordQubit_inl (i : ι) : coordQubit (Sum.inl i : ι ⊕ ι) = i := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coordQubit_inr (i : ι) : coordQubit (Sum.inr i : ι ⊕ ι) = i := rfl

/-- A `2n × 2n` matrix `G` over `𝔽₂` (coordinates `ι ⊕ ι`, the polarized `X | Z` split) is
`M`-**block-diagonal** for the matching (involution) `σ` when its entry `G p q` vanishes whenever
the qubits carrying coordinates `p` and `q` lie in different cells of `M`, i.e. whenever
`coordQubit q ≠ coordQubit p` and `coordQubit q ≠ σ (coordQubit p)`. This is the "reorder the
coordinates so each qubit's `X, Z` sit together, then `G` is block-diagonal with one `Sp(4)` block
per matched pair and one `Sp(2)` block per singleton" description of §D.1; the equivalent
"`A, B, C, D` block reading" is `isSpBlockDiagonal_fromBlocks_iff`. -/
def IsSpBlockDiagonal (σ : Equiv.Perm ι) (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) : Prop :=
  ∀ p q : ι ⊕ ι, coordQubit q ≠ coordQubit p → coordQubit q ≠ σ (coordQubit p) → G p q = 0

omit [Fintype ι] [DecidableEq ι] in
/-- **Convention c4, the block reading.** A block matrix `G = [[A, B], [C, D]]` is
`M`-block-diagonal iff each of its four `n × n` blocks `A, B, C, D` is `M`-block-diagonal
(`IsCellDiagonal σ`). This is
the paper's concrete definition of `𝒟_M` in the `X̂ | Ẑ` convention, tied to the coordinate-level
predicate `IsSpBlockDiagonal`. -/
theorem isSpBlockDiagonal_fromBlocks_iff {σ : Equiv.Perm ι} (A B C D : Matrix ι ι (ZMod 2)) :
    IsSpBlockDiagonal σ (Matrix.fromBlocks A B C D) ↔
      IsCellDiagonal σ A ∧ IsCellDiagonal σ B ∧ IsCellDiagonal σ C ∧ IsCellDiagonal σ D := by
  constructor
  · intro h
    refine ⟨fun i j hji hjσ => ?_, fun i j hji hjσ => ?_, fun i j hji hjσ => ?_,
      fun i j hji hjσ => ?_⟩
    · have := h (Sum.inl i) (Sum.inl j) (by simpa using hji) (by simpa using hjσ)
      simpa [Matrix.fromBlocks_apply₁₁] using this
    · have := h (Sum.inl i) (Sum.inr j) (by simpa using hji) (by simpa using hjσ)
      simpa [Matrix.fromBlocks_apply₁₂] using this
    · have := h (Sum.inr i) (Sum.inl j) (by simpa using hji) (by simpa using hjσ)
      simpa [Matrix.fromBlocks_apply₂₁] using this
    · have := h (Sum.inr i) (Sum.inr j) (by simpa using hji) (by simpa using hjσ)
      simpa [Matrix.fromBlocks_apply₂₂] using this
  · rintro ⟨hA, hB, hC, hD⟩ p q hpq hpqσ
    cases p with
    | inl i =>
      cases q with
      | inl j =>
        simp only [coordQubit_inl] at hpq hpqσ
        rw [Matrix.fromBlocks_apply₁₁]; exact hA i j hpq hpqσ
      | inr j =>
        simp only [coordQubit_inl, coordQubit_inr] at hpq hpqσ
        rw [Matrix.fromBlocks_apply₁₂]; exact hB i j hpq hpqσ
    | inr i =>
      cases q with
      | inl j =>
        simp only [coordQubit_inl, coordQubit_inr] at hpq hpqσ
        rw [Matrix.fromBlocks_apply₂₁]; exact hC i j hpq hpqσ
      | inr j =>
        simp only [coordQubit_inr] at hpq hpqσ
        rw [Matrix.fromBlocks_apply₂₂]; exact hD i j hpq hpqσ

omit [Fintype ι] in
/-- The identity `n × n` matrix is `M`-block-diagonal for every matching: its off-diagonal entries
vanish, and the diagonal lies inside every cell. -/
theorem isCellDiagonal_one (σ : Equiv.Perm ι) :
    IsCellDiagonal σ (1 : Matrix ι ι (ZMod 2)) :=
  fun _ _ hji _ => Matrix.one_apply_ne' hji

omit [Fintype ι] [DecidableEq ι] in
/-- The zero matrix is `M`-block-diagonal for every matching. -/
theorem isCellDiagonal_zero (σ : Equiv.Perm ι) :
    IsCellDiagonal σ (0 : Matrix ι ι (ZMod 2)) :=
  fun _ _ _ _ => rfl

/-! ### Closure of `IsCellDiagonal` under sum, product, transpose and inverse

The `n × n` block-diagonal predicate `IsCellDiagonal σ` is closed under the ring operations (sum,
product) and under transpose and matrix inverse — a genuine block-diagonal *subalgebra*, closed
under units. These are the closure facts needed to reduce the block-diagonality of a *Levi* gate
`Levi(K) = [[K, 0], [0, K⁻ᵀ]]` to that of its single parameter `K` (`leviGate_isSpBlockDiagonal_iff`
below): the lower-right block `K⁻ᵀ` is `M`-block-diagonal as soon as `K` is. They also feed the
block-diagonality half of Lemma D.2 (`BeyondTransversalityAutoParams`). -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Sum closure.** The `M`-block-diagonal matrices are closed under sum: `IsCellDiagonal σ` is an
entrywise "equals `0` off the cells" constraint, preserved by addition. -/
theorem isCellDiagonal_add {σ : Equiv.Perm ι} {S T : Matrix ι ι (ZMod 2)}
    (hS : IsCellDiagonal σ S) (hT : IsCellDiagonal σ T) : IsCellDiagonal σ (S + T) :=
  fun i j hji hjσ => by rw [Matrix.add_apply, hS i j hji hjσ, hT i j hji hjσ, add_zero]

omit [DecidableEq ι] in
/-- **Product closure.** The `M`-block-diagonal matrices are closed under multiplication (using the
involutivity of `σ`). In `(S T) i j = ∑ k, S i k · T k j`, a term survives only if `k`'s qubit is in
`i`'s cell (else `S i k = 0`); the two options `k = i` and `k = σ i` both force `T k j = 0` when `j`
is off `i`'s cell (for `k = σ i` via `σ (σ i) = i`). -/
theorem isCellDiagonal_mul {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    {S T : Matrix ι ι (ZMod 2)} (hS : IsCellDiagonal σ S) (hT : IsCellDiagonal σ T) :
    IsCellDiagonal σ (S * T) := by
  intro i j hji hjσ
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : k = i
  · subst h1; rw [hT k j hji hjσ, mul_zero]
  · by_cases h2 : k = σ i
    · subst h2; rw [hT (σ i) j hjσ (by rw [hσ i]; exact hji), mul_zero]
    · rw [hS i k h1 h2, zero_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- **Transpose closure.** The `M`-block-diagonal matrices are closed under transpose (using the
involutivity of `σ`): `Sᵀ i j = S j i`, and the cell relation is symmetric (`σ² = id`), so the
vanishing condition on `S j i` follows from the one on the cell of `j`. -/
theorem isCellDiagonal_transpose {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    {S : Matrix ι ι (ZMod 2)} (hS : IsCellDiagonal σ S) : IsCellDiagonal σ Sᵀ := by
  intro i j hji hjσ
  rw [Matrix.transpose_apply]
  refine hS j i (Ne.symm hji) ?_
  intro h
  exact hjσ (by rw [h, hσ j])


omit [Fintype ι] in
/-- The identity symplectic matrix `1` is `M`-block-diagonal for every matching. -/
theorem isSpBlockDiagonal_one (σ : Equiv.Perm ι) :
    IsSpBlockDiagonal σ (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) :=
  fun _ _ hpq _ => Matrix.one_apply_ne' fun h => hpq (congrArg coordQubit h)

omit [DecidableEq ι] in
/-- **Product closure.** The `M`-block-diagonal matrices are closed under multiplication. In the sum
`(G H) p q = ∑ r, G p r · H r q`, a term survives only if `r`'s qubit is in the cell of `p`'s qubit
(else `G p r = 0`) *and* in the cell of `q`'s qubit (else `H r q = 0`); the cell relation being an
equivalence (using `σ² = id`), those two cells would coincide, contradicting `q`'s qubit being in a
different cell from `p`'s. -/
theorem isSpBlockDiagonal_mul {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    {G H : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} (hG : IsSpBlockDiagonal σ G)
    (hH : IsSpBlockDiagonal σ H) : IsSpBlockDiagonal σ (G * H) := by
  intro p q hpq hpqσ
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases h1 : coordQubit r = coordQubit p
  · have e1 : coordQubit q ≠ coordQubit r := by rw [h1]; exact hpq
    have e2 : coordQubit q ≠ σ (coordQubit r) := by rw [h1]; exact hpqσ
    rw [hH r q e1 e2, mul_zero]
  · by_cases h2 : coordQubit r = σ (coordQubit p)
    · have e1 : coordQubit q ≠ coordQubit r := by rw [h2]; exact hpqσ
      have e2 : coordQubit q ≠ σ (coordQubit r) := by rw [h2, hσ]; exact hpq
      rw [hH r q e1 e2, mul_zero]
    · rw [hG p r h1 h2, zero_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- **Transpose closure.** The `M`-block-diagonal matrices are closed under transpose: `Gᵀ p q =
G q p`, and the cell relation is symmetric (using `σ² = id`), so the vanishing condition on `G q p`
follows from the one on `G p q`. -/
theorem isSpBlockDiagonal_transpose {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    {G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)} (hG : IsSpBlockDiagonal σ G) :
    IsSpBlockDiagonal σ Gᵀ := by
  intro p q hpq hpqσ
  rw [Matrix.transpose_apply]
  refine hG q p (fun h => hpq h.symm) ?_
  intro h
  apply hpqσ
  rw [h, hσ]

omit [Fintype ι] in
/-- The paper's Gram matrix `J = symplecticMatrix = [[0, I], [I, 0]]` is `M`-block-diagonal for
every matching: it links only the two same-qubit coordinates `inl i ↔ inr i`, which always share a
cell. (Via the block reading: the four blocks `0, I, I, 0` are each `IsCellDiagonal σ`.) -/
theorem isSpBlockDiagonal_symplecticMatrix (σ : Equiv.Perm ι) :
    IsSpBlockDiagonal σ (symplecticMatrix : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) := by
  rw [symplecticMatrix, isSpBlockDiagonal_fromBlocks_iff]
  exact ⟨isCellDiagonal_zero σ, isCellDiagonal_one σ, isCellDiagonal_one σ, isCellDiagonal_zero σ⟩

/-- The **`M`-block-diagonal symplectic subgroup** `𝒟_M = Sp(2n)_M` of *Beyond transversality*
(§D.1, Convention c4): the subgroup of the binary symplectic group `Sp(2n, 𝔽₂)`
(`binarySymplecticGroup`) whose matrices are `M`-block-diagonal, for a matching `M` given by an
involution `σ` (`hσ : σ² = id`). It is a genuine subgroup: `1` is block-diagonal
(`isSpBlockDiagonal_one`), the block-diagonal matrices are closed under product
(`isSpBlockDiagonal_mul`, using the involutivity of `σ`), and under the `𝔽₂` symplectic inverse
`G⁻¹ = J Gᵀ J` (`isSpBlockDiagonal_transpose` and `isSpBlockDiagonal_symplecticMatrix`, with
`-J = J` in characteristic two). The membership characterization matching the paper's `X̂ | Ẑ` block
definition is `mem_blockDiagonalSymplecticGroup_fromBlocks_iff`. -/
def blockDiagonalSymplecticGroup (σ : Equiv.Perm ι) (hσ : Function.Involutive σ) :
    Subgroup ↥(binarySymplecticGroup ι) where
  carrier := {G | IsSpBlockDiagonal σ (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))}
  mul_mem' {G H} hG hH := by
    change IsSpBlockDiagonal σ
      ((G * H : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
    rw [Submonoid.coe_mul]
    exact isSpBlockDiagonal_mul hσ hG hH
  one_mem' := by
    change IsSpBlockDiagonal σ ((1 : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
    rw [Submonoid.coe_one]
    exact isSpBlockDiagonal_one σ
  inv_mem' {G} hG := by
    change IsSpBlockDiagonal σ
      ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
    rw [SymplecticGroup.coe_inv, neg_eq_self_zmod2, J_eq_symplecticMatrix]
    exact isSpBlockDiagonal_mul hσ
      (isSpBlockDiagonal_mul hσ (isSpBlockDiagonal_symplecticMatrix σ)
        (isSpBlockDiagonal_transpose hσ hG))
      (isSpBlockDiagonal_symplecticMatrix σ)

@[simp] theorem mem_blockDiagonalSymplecticGroup_iff {σ : Equiv.Perm ι}
    (hσ : Function.Involutive σ) {G : ↥(binarySymplecticGroup ι)} :
    G ∈ blockDiagonalSymplecticGroup σ hσ ↔
      IsSpBlockDiagonal σ (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) :=
  Iff.rfl


/-! ### Block-diagonality of the shear generators -/

omit [Fintype ι] in
/-- **The `Z`-shear `U_Z(B) = [[I, B], [0, I]]` is `M`-block-diagonal iff its parameter is.** Its
four blocks are `I`, `B`, `0`, `I`, so `isSpBlockDiagonal_fromBlocks_iff` reduces
`IsSpBlockDiagonal σ (shearZ B)` to `IsCellDiagonal σ B` (`I`, `0` are `M`-block-diagonal for every
matching). Reused wherever a shear on the matching enters a block-diagonal product (the assembly
word `W`, the terminal factorization). -/
theorem shearZ_isSpBlockDiagonal {σ : Equiv.Perm ι} {B : Matrix ι ι (ZMod 2)}
    (hB : IsCellDiagonal σ B) : IsSpBlockDiagonal σ (shearZ B) := by
  rw [shearZ, isSpBlockDiagonal_fromBlocks_iff]
  exact ⟨isCellDiagonal_one σ, hB, isCellDiagonal_zero σ, isCellDiagonal_one σ⟩


omit [Fintype ι] in
/-- **The `X`-shear `L_X(C) = [[I, 0], [C, I]]` is `M`-block-diagonal iff its parameter is** (dual
to `shearZ_isSpBlockDiagonal`): its four blocks are `I`, `0`, `C`, `I`. -/
theorem shearX_isSpBlockDiagonal {σ : Equiv.Perm ι} {C : Matrix ι ι (ZMod 2)}
    (hC : IsCellDiagonal σ C) : IsSpBlockDiagonal σ (shearX C) := by
  rw [shearX, isSpBlockDiagonal_fromBlocks_iff]
  exact ⟨isCellDiagonal_one σ, isCellDiagonal_zero σ, hC, isCellDiagonal_one σ⟩


/-! ### Block-diagonality of the Levi gate -/


end CliffordCSS

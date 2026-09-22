import CliffordCSS.DepthOne.Restrict
import CliffordCSS.DepthOne.TerminalNormalForm
import CliffordCSS.ToMathlib.Data.Matrix.CharTwo
import Mathlib.LinearAlgebra.Matrix.Unique
import CliffordCSS.ToMathlib.LinearAlgebra.Matrix.Unique

/-!
# Local moves and the local-reduction hypothesis (Beyond transversality, App. D.1 — D.4)

Pure mathematics : the **move graph** on a single symplectic
block and the exact statement of **Lemma D.4 (Local reduction)** of *Beyond transversality*
(arXiv:2608.05688), `𝔽₂` symplectic linear algebra.

## The move graph on one block

Fix a finite index type `κ` — the coordinates of a **single cell**, of width `w = |κ| ∈ {1, 2}`
for a `2`-local layer. A *block* is a matrix `g ∈ Sp(2w, 𝔽₂)` on `κ ⊕ κ`; its four `w × w` blocks
are `A = g.toBlocks₁₁`, `B = g.toBlocks₁₂`, `C = g.toBlocks₂₁`, `D = g.toBlocks₂₂`. Out of those
blocks the construction of Lemma D.2 manufactures the two parameter spans
`Θ^Z(g) = span {A Bᵀ, Dᵀ B, B + Bᵀ}` and `Θ^X(g) = span {C Dᵀ, Cᵀ A, C + Cᵀ}`, enumerated by the
coefficient vector `ε ∈ 𝔽₂³` through the formulas `S^Z(g, ε)` (`layerZParam`) and `S^X(g, ε)`
(`layerXParam`) of Eq. (d1-eps). A **move** (Eq. (d1-moves), `IsBlockMove`) is a left or right
multiplication by the diagonal circuit `U_Z(S)` / `L_X(T)` of a **nonzero** such parameter: a
family, a nonzero coefficient vector, and a side. The moves available at a block are manufactured
from that block itself, so the edges leaving a vertex change as the walk proceeds — "this is not a
graph with a fixed set of steps, which is why reachability has to be decided rather than read
off". The walk halts at the **terminal** blocks (`IsTerminalLayer`, Eq. (d1-term)), on which all
six generators vanish and which are therefore fixed by every move.

`ReachesTerminalIn k g` is "`g` reaches a terminal block in at most `k` moves"; it is monotone in
`k` (`ReachesTerminalIn.mono`). Terminality is **absorbing**:
`spzParam_eq_zero_of_isTerminalBlock` and its `X` dual say that every parameter available at a
terminal block is `0`, so a terminal block is fixed by every move — this file is the lowest one
naming both the parameter formulas (`BeyondTransversalityRestrict`) and `IsTerminalBlock`
(`BeyondTransversalityTerminal`).

## Lemma D.4 as a hypothesis, and what is proved here

`LocalReduction w k` says: *every* block of width `w` reaches a terminal block in at most `k` moves.
Lemma D.4 is exactly `LocalReduction 1 1 ∧ LocalReduction 2 3` ("Every element of `Sp(2)` reaches a
terminal block in at most one move; … every element of `Sp(4)` … in at most three moves"). The
statement mentions **only** a symplectic block, the moves manufactured from its own six parameters,
terminality and a move bound — no code `C_X`/`C_Z`, no matching, no family: it is a self-contained
claim about `Sp(2w, 𝔽₂)`, as in the paper.

The paper proves it by exhaustive machine enumeration of the `6 + 720` blocks ("this is checked for
every one of the `720 + 6` elements"), which is out of reach for the kernel here.lean`. The
width-two half is therefore
left as a hypothesis, to be discharged by whoever can certify `Sp(4)`. The **width-one half is
proved** here — *both* of its clauses, the reachability bound (`localReduction_width_one`) and the
count (`terminalBlocks_width_one`, "there are two terminal blocks") — so downstream results need
only `LocalReduction 2 3`. Of the width-two half neither clause is formalized: the reachability
bound is the hypothesis, and "there are sixteen terminal blocks" is asserted nowhere.

* `reachesTerminalIn_one_of_lowerLeft_zero` / `reachesTerminalIn_one_of_upperRight_zero` — the two
  *symbolic* strata of Table (d1-strata), at **every** width: a block with `C = 0` (resp. `B = 0`)
  is terminal or reaches a Levi block in one move, by the closed-form rules of Lemma D.3.
* `localReduction_width_one` — Lemma D.4's **reachability** clause at `w = 1`: the two strata above
  cover every block with `B = 0` or `C = 0`; at width one the remaining blocks have `B = C = 1`,
  whence `A D = 0` by Eq. (d1-sympl), and the three surviving cases are the terminal swap
  `[[0,1],[1,0]]` and two blocks one move from it (right `U_Z(Dᵀ B)` for `A = 0`, left `U_Z(A Bᵀ)`
  for `D = 0`).
* `isTerminalLayer_width_one_iff` / `terminalBlocks_width_one` / `one_ne_symplecticMatrix` —
  Lemma D.4's **count** clause at `w = 1`: the terminal blocks of `Sp(2, 𝔽₂)` are exactly the
  identity and the swap `[[0,1],[1,0]]` — the Gram matrix `CliffordCSS.symplecticMatrix`, this
  library's canonical spelling of `[[0, I], [I, 0]]` — and those two are distinct: "there are two
  terminal blocks".

No orthogonality `C_X ⊥ C_Z` is used, and no property of a code enters: "a statement about split
subspaces and nothing more".
-/

open Matrix

namespace CliffordCSS

universe u

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### The parameter formulas and terminality, read off a block -/

/-- The **`Z`-parameter** `S^Z(g, ε) = ε₁·A Bᵀ + ε₂·Dᵀ B + ε₃·(B + Bᵀ)` (Eq. (d1-eps)) of a block
`g`, with its blocks `A = g.toBlocks₁₁`, `B = g.toBlocks₁₂`, `D = g.toBlocks₂₂` read off `g` itself.
As `ε` ranges over `𝔽₂³` its values are exactly the manufactured span
`Θ^Z(g) = span {A Bᵀ, Dᵀ B, B + Bᵀ}` of Lemma D.2. -/
def layerZParam (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) (ε : Fin 3 → ZMod 2) : Matrix κ κ (ZMod 2) :=
  spzParam g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₂ ε

/-- The **`X`-parameter** `S^X(g, ε) = ε₁·C Dᵀ + ε₂·Cᵀ A + ε₃·(C + Cᵀ)` (Eq. (d1-eps)) of a block
`g`, the `X ↔ Z` dual of `layerZParam`; its `ε`-range is `Θ^X(g) = span {C Dᵀ, Cᵀ A, C + Cᵀ}`. -/
def layerXParam (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) (ε : Fin 3 → ZMod 2) : Matrix κ κ (ZMod 2) :=
  spxParam g.toBlocks₁₁ g.toBlocks₂₁ g.toBlocks₂₂ ε

/-- A block `g` is **terminal** (Eq. (d1-term)) when all six manufactured generators vanish on its
own blocks, i.e. `IsTerminalBlock g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂`. Every
parameter available at a terminal block is then `0`, so it is fixed by every move. -/
def IsTerminalLayer (g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) : Prop :=
  IsTerminalBlock g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂

omit [DecidableEq κ] in
/-- Reading the `Z`-parameter off a block presented in block form: `S^Z([[A, B], [C, D]], ε)` is
the parameter formula `spzParam A B D ε` of Eq. (d1-eps). -/
@[simp] theorem layerZParam_fromBlocks (A B C D : Matrix κ κ (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    layerZParam (Matrix.fromBlocks A B C D) ε = spzParam A B D ε := rfl

omit [DecidableEq κ] in
/-- Reading the `X`-parameter off a block presented in block form: `S^X([[A, B], [C, D]], ε)` is
the parameter formula `spxParam A C D ε` of Eq. (d1-eps). -/
@[simp] theorem layerXParam_fromBlocks (A B C D : Matrix κ κ (ZMod 2)) (ε : Fin 3 → ZMod 2) :
    layerXParam (Matrix.fromBlocks A B C D) ε = spxParam A C D ε := rfl

omit [DecidableEq κ] in
/-- Terminality of a block presented in block form is terminality of its four blocks
(Eq. (d1-term)). -/
@[simp] theorem isTerminalLayer_fromBlocks (A B C D : Matrix κ κ (ZMod 2)) :
    IsTerminalLayer (Matrix.fromBlocks A B C D) ↔ IsTerminalBlock A B C D := Iff.rfl

omit [DecidableEq κ] in
/-- **Every `Z`-parameter vanishes on a terminal block**: all three generators of `Θ^Z` are `0`
there (Eq. (d1-term)), so every `ε`-combination is `0`. This is the paper's "a finished cell can
never be disturbed again": a later move, whatever `ε` it selects, restricts to `U_Z(0) = I` on a
terminal cell. -/
theorem spzParam_eq_zero_of_isTerminalBlock {A B C D : Matrix κ κ (ZMod 2)}
    (h : IsTerminalBlock A B C D) (ε : Fin 3 → ZMod 2) : spzParam A B D ε = 0 := by
  obtain ⟨h1, h2, h3, _, _, _⟩ := h
  rw [spzParam, h1, h2, h3, smul_zero, smul_zero, smul_zero, add_zero, add_zero]

omit [DecidableEq κ] in
/-- **Every `X`-parameter vanishes on a terminal block** (dual to
`spzParam_eq_zero_of_isTerminalBlock`). -/
theorem spxParam_eq_zero_of_isTerminalBlock {A B C D : Matrix κ κ (ZMod 2)}
    (h : IsTerminalBlock A B C D) (ε : Fin 3 → ZMod 2) : spxParam A C D ε = 0 := by
  obtain ⟨_, _, _, h4, h5, h6⟩ := h
  rw [spxParam, h4, h5, h6, smul_zero, smul_zero, smul_zero, add_zero, add_zero]

/-! ### Moves and bounded reachability -/

/-- A **move** (Eq. (d1-moves)) from the block `g` to the block `g'`: a family (`Z`-diagonal or
`X`-diagonal), a **nonzero** parameter of that family manufactured from `g`'s own blocks — indexed
by a coefficient vector `ε ∈ 𝔽₂³` — and a side (left or right multiplication). Since the parameter
is recomputed from the current block, the edge set of this graph changes as the walk proceeds. -/
def IsBlockMove (g g' : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) : Prop :=
  (∃ ε : Fin 3 → ZMod 2, layerZParam g ε ≠ 0 ∧
      (g' = shearZ (layerZParam g ε) * g ∨ g' = g * shearZ (layerZParam g ε))) ∨
  (∃ ε : Fin 3 → ZMod 2, layerXParam g ε ≠ 0 ∧
      (g' = shearX (layerXParam g ε) * g ∨ g' = g * shearX (layerXParam g ε)))

/-- `ReachesTerminalIn k g`: the block `g` **reaches a terminal block in at most `k` moves**, i.e.
its distance to the terminal set (the least number of moves carrying it there) is at most `k`. -/
def ReachesTerminalIn : ℕ → Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2) → Prop
  | 0, g => IsTerminalLayer g
  | n + 1, g => IsTerminalLayer g ∨ ∃ g', IsBlockMove g g' ∧ ReachesTerminalIn n g'

@[simp] theorem reachesTerminalIn_zero {g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)} :
    ReachesTerminalIn 0 g ↔ IsTerminalLayer g := Iff.rfl

@[simp] theorem reachesTerminalIn_succ {n : ℕ} {g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)} :
    ReachesTerminalIn (n + 1) g ↔
      IsTerminalLayer g ∨ ∃ g', IsBlockMove g g' ∧ ReachesTerminalIn n g' := Iff.rfl

/-- **A larger move budget is a weaker requirement**: reaching a terminal block in at most `k` moves
implies reaching one in at most `k'` moves whenever `k ≤ k'`. This is what makes `ReachesTerminalIn`
an "at most `k` moves" predicate rather than an "exactly `k`" one. -/
theorem ReachesTerminalIn.mono {k k' : ℕ} {g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)}
    (h : ReachesTerminalIn k g) (hk : k ≤ k') : ReachesTerminalIn k' g := by
  induction k generalizing k' g with
  | zero =>
    cases k' with
    | zero => exact h
    | succ n => exact Or.inl h
  | succ k ih =>
    cases k' with
    | zero => exact absurd hk (Nat.not_succ_le_zero k)
    | succ n =>
      rcases h with hterm | ⟨g', hmove, hreach⟩
      · exact Or.inl hterm
      · exact Or.inr ⟨g', hmove, ih hreach (Nat.le_of_succ_le_succ hk)⟩

/-- **Lemma D.4 (Local reduction) as a statement about one cell block**, at width `w` with move
bound `k`: every symplectic block on an index type of cardinality `w` reaches a terminal block in at
most `k` moves. The paper's Lemma D.4 is `LocalReduction 1 1 ∧ LocalReduction 2 3`.

The statement quantifies over an arbitrary index type of the given cardinality, so it applies to the
coordinates of any cell; it mentions only the block, the moves manufactured from the block's own six
parameters, terminality and the move bound — no code, no matching, no generating family. -/
def LocalReduction (w k : ℕ) : Prop :=
  ∀ (κ : Type u) [Fintype κ] [DecidableEq κ], Fintype.card κ = w →
    ∀ g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2), g ∈ binarySymplecticGroup κ → ReachesTerminalIn k g

/-! ### The two closed-form strata of Lemma D.3, at every width -/

/-- **The `C = 0` stratum reaches a terminal block in one move, at every width.** For a symplectic
block `g = [[A, B], [0, D]]`, the closed-form parameter `S = Dᵀ B = A⁻¹ B` of Lemma D.3
(`dragToLevi_of_lowerLeft_zero`) is the value of `S^Z(g, ε)` at `ε = (0, 1, 0)`, and
`g · U_Z(S) = [[A, 0], [0, D]]` is a Levi block, hence terminal. If `S = 0` the "move" is trivial
and `g` is itself that Levi block, so `g` is already terminal. This is the symbolic row
`g ↦ g U_Z(Dᵀ B)` of Table (d1-strata). -/
theorem reachesTerminalIn_one_of_lowerLeft_zero {A B D : Matrix κ κ (ZMod 2)}
    (hsymp : Matrix.fromBlocks A B 0 D ∈ binarySymplecticGroup κ) :
    ReachesTerminalIn 1 (Matrix.fromBlocks A B 0 D) := by
  obtain ⟨-, -, hmove⟩ := dragToLevi_of_lowerLeft_zero hsymp
  have hparam : spzParam A B D ![0, 1, 0] = Dᵀ * B := by
    simp [spzParam]
  by_cases hS : Dᵀ * B = 0
  · refine Or.inl ?_
    rw [hS, shearZ_zero, Matrix.mul_one] at hmove
    rw [hmove]
    exact isTerminalBlock_of_offDiag_zero A D
  · refine Or.inr ⟨Matrix.fromBlocks A 0 0 D, Or.inl ⟨![0, 1, 0], ?_, Or.inr ?_⟩, ?_⟩
    · rw [layerZParam_fromBlocks, hparam]; exact hS
    · rw [layerZParam_fromBlocks, hparam]; exact hmove.symm
    · exact isTerminalBlock_of_offDiag_zero A D

/-- **The `B = 0` stratum reaches a terminal block in one move, at every width** (dual to
`reachesTerminalIn_one_of_lowerLeft_zero`). For a symplectic block `g = [[A, 0], [C, D]]` the
closed-form parameter `T = Cᵀ A` of Lemma D.3 (`dragToLevi_of_upperRight_zero`) is `S^X(g, ε)` at
`ε = (0, 1, 0)` and `g · L_X(T) = [[A, 0], [0, D]]` is Levi, hence terminal; if `T = 0` then `g` is
already that Levi block. This is the symbolic row `g ↦ g L_X(Cᵀ A)` of Table (d1-strata). -/
theorem reachesTerminalIn_one_of_upperRight_zero {A C D : Matrix κ κ (ZMod 2)}
    (hsymp : Matrix.fromBlocks A 0 C D ∈ binarySymplecticGroup κ) :
    ReachesTerminalIn 1 (Matrix.fromBlocks A 0 C D) := by
  obtain ⟨-, -, hmove⟩ := dragToLevi_of_upperRight_zero hsymp
  have hparam : spxParam A C D ![0, 1, 0] = Cᵀ * A := by
    simp [spxParam]
  by_cases hT : Cᵀ * A = 0
  · refine Or.inl ?_
    rw [hT, shearX_zero, Matrix.mul_one] at hmove
    rw [hmove]
    exact isTerminalBlock_of_offDiag_zero A D
  · refine Or.inr ⟨Matrix.fromBlocks A 0 0 D, Or.inr ⟨![0, 1, 0], ?_, Or.inr ?_⟩, ?_⟩
    · rw [layerXParam_fromBlocks, hparam]; exact hT
    · rw [layerXParam_fromBlocks, hparam]; exact hmove.symm
    · exact isTerminalBlock_of_offDiag_zero A D

/-! ### Lemma D.4 at width one -/

/-- **The swap block `Λ = [[0, 1], [1, 0]]` is terminal** — the second of the two terminal blocks of
`Sp(2, 𝔽₂)` (the first being the identity), and the target of both width-one moves below. It is the
Gram matrix `symplecticMatrix` of Nielsen & Chuang eq. (10.84), this library's canonical spelling of
`[[0, I], [I, 0]]`. All six generators of Eq. (d1-term) vanish: the four products contain a zero
factor, and the two symmetrizations are `1 + 1 = 0`. -/
theorem isTerminalLayer_symplecticMatrix :
    IsTerminalLayer (symplecticMatrix : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)) := by
  rw [symplecticMatrix]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Matrix.add_self_eq_zero]

/-- **Lemma D.4 at width one, the reachability clause: every element of `Sp(2, 𝔽₂)` reaches a
terminal block in at most one move.** The blocks with `B = 0` or `C = 0` are covered at every width
by the closed-form strata (`reachesTerminalIn_one_of_upperRight_zero` / `…_lowerLeft_zero`), which
land on the Levi block `[[A, 0], [0, D]]` — at width one necessarily the **identity**, since
`A Dᵀ = I` forces `A = D = 1`. At width one every `1 × 1` matrix is `0` or `1`
(`Matrix.eq_zero_or_one_of_unique`), so in the remaining case `B = C = 1`; the symplectic relation
`A Dᵀ + B Cᵀ = I` (Eq. (d1-sympl)) then forces `A D = 0`, leaving three blocks: the swap
`[[0,1],[1,0]]`, which is terminal; `[[0,1],[1,1]]`, carried to the swap by the right move
`U_Z(Dᵀ B)`; and `[[1,1],[1,0]]`, carried to the swap by the left move `U_Z(A Bᵀ)`. This is the
paper's "max distance one" at `w = 1` (Table (d1-strata)); the companion clause "there are two
terminal blocks" — the identity and the swap — is `terminalBlocks_width_one`. -/
theorem localReduction_width_one : LocalReduction.{u} 1 1 := by
  intro κ _ _ hcard g hg
  obtain ⟨huniq⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hcard
  letI := huniq
  obtain ⟨A, B, C, D, rfl⟩ :
      ∃ A B C D : Matrix κ κ (ZMod 2), g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rcases Matrix.eq_zero_or_one_of_unique B with rfl | rfl
  · exact reachesTerminalIn_one_of_upperRight_zero hg
  rcases Matrix.eq_zero_or_one_of_unique C with rfl | rfl
  · exact reachesTerminalIn_one_of_lowerLeft_zero hg
  -- `B = C = 1`: the symplectic relation `A Dᵀ + B Cᵀ = I` becomes `A D = 0`
  obtain ⟨-, -, hrel⟩ := (fromBlocks_mem_binarySymplecticGroup_iff A 1 1 D).mp hg
  rw [Matrix.transpose_one, Matrix.one_mul] at hrel
  have hAD : A * Dᵀ = 0 := add_eq_right.mp hrel
  rcases Matrix.eq_zero_or_one_of_unique A with rfl | rfl
  · rcases Matrix.eq_zero_or_one_of_unique D with rfl | rfl
    · -- the swap `[[0, 1], [1, 0]]` is terminal
      exact Or.inl isTerminalLayer_symplecticMatrix
    · -- `[[0, 1], [1, 1]]`: the right move `U_Z(Dᵀ B) = U_Z(1)` lands on the swap
      have hS : spzParam (0 : Matrix κ κ (ZMod 2)) 1 1 ![0, 1, 0] = 1 := by simp [spzParam]
      refine Or.inr ⟨symplecticMatrix, Or.inl ⟨![0, 1, 0], ?_, Or.inr ?_⟩, ?_⟩
      · rw [layerZParam_fromBlocks, hS]; exact one_ne_zero
      · rw [layerZParam_fromBlocks, hS, shearZ, Matrix.fromBlocks_multiply, symplecticMatrix]
        simp [Matrix.add_self_eq_zero]
      · exact isTerminalLayer_symplecticMatrix
  · rcases Matrix.eq_zero_or_one_of_unique D with rfl | rfl
    · -- `[[1, 1], [1, 0]]`: the left move `U_Z(A Bᵀ) = U_Z(1)` lands on the swap
      have hS : spzParam (1 : Matrix κ κ (ZMod 2)) 1 0 ![1, 0, 0] = 1 := by simp [spzParam]
      refine Or.inr ⟨symplecticMatrix, Or.inl ⟨![1, 0, 0], ?_, Or.inl ?_⟩, ?_⟩
      · rw [layerZParam_fromBlocks, hS]; exact one_ne_zero
      · rw [layerZParam_fromBlocks, hS, shearZ, Matrix.fromBlocks_multiply, symplecticMatrix]
        simp [Matrix.add_self_eq_zero]
      · exact isTerminalLayer_symplecticMatrix
    · -- `A = D = 1` contradicts `A D = 0`
      rw [Matrix.transpose_one, Matrix.mul_one] at hAD
      exact absurd hAD (one_ne_zero (α := Matrix κ κ (ZMod 2)))

/-! ### Lemma D.4 at width one, the count clause: there are two terminal blocks -/


/-- **The terminal blocks at width one are exactly the identity and the swap.** Forward: a terminal
symplectic block over a one-element index type is `Id` or `U_Z(1) L_X(1) U_Z(1) = [[0,1],[1,0]]`
(Lemma D.7, `terminalNormalForm_width_one`). Backward: the identity is a Levi block, hence terminal
(`isTerminalBlock_of_offDiag_zero`), and the swap is terminal
(`isTerminalLayer_symplecticMatrix`). -/
theorem isTerminalLayer_width_one_iff [Unique κ] {g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2)}
    (hg : g ∈ binarySymplecticGroup κ) :
    IsTerminalLayer g ↔ g = 1 ∨ g = symplecticMatrix := by
  obtain ⟨A, B, C, D, rfl⟩ :
      ∃ A B C D : Matrix κ κ (ZMod 2), g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  constructor
  · intro hterm
    rcases terminalNormalForm_width_one hg hterm with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, word_one_one])
  · rintro (h | h) <;> rw [h]
    · rw [← Matrix.fromBlocks_one]
      exact isTerminalBlock_of_offDiag_zero 1 1
    · exact isTerminalLayer_symplecticMatrix

/-- **Lemma D.4's count clause at width one: "there are two terminal blocks".** The terminal
elements of `Sp(2, 𝔽₂)` are exactly the pair `{Id, [[0,1],[1,0]]}`, whose two members are distinct
(`one_ne_symplecticMatrix`). -/
theorem terminalBlocks_width_one [Unique κ] :
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) (ZMod 2) | g ∈ binarySymplecticGroup κ ∧ IsTerminalLayer g}
      = {1, symplecticMatrix} := by
  ext g
  constructor
  · rintro ⟨hg, hterm⟩
    exact (isTerminalLayer_width_one_iff hg).mp hterm
  · rintro (rfl | rfl)
    · exact ⟨one_mem _, (isTerminalLayer_width_one_iff (one_mem _)).mpr (Or.inl rfl)⟩
    · exact ⟨symplecticMatrix_mem_binarySymplecticGroup, isTerminalLayer_symplecticMatrix⟩

end CliffordCSS

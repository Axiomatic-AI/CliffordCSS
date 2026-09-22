import CliffordCSS.DepthOne.ShearLevi
import CliffordCSS.DepthOne.Supply

/-!
# Terminal blocks and the two closed-form cases
(Beyond transversality, App. D.1 — the terminal predicate and Lemma D.3)

Pure mathematics : two ingredients of the *reduction by
multiplication* proof of the fixed-matching generation theorem (Theorem D.1, `thm-depthone`) of
*Beyond transversality* (arXiv:2608.05688) — the **terminal-block predicate** (Eq. (d1-term)) and
**Lemma D.3 (Two closed-form cases)**. Everything is `𝔽₂` symplectic linear algebra naming the raw
carrier `Matrix`.

## Terminal blocks (Eq. (d1-term))

The reduction of §D.1 is a *walk*: a block `g = [[A, B], [C, D]]` is multiplied on left/right by
`Z`- and `X`-diagonal circuits whose parameters are manufactured from `g`'s own blocks (Lemma D.2),
and the walk halts when all six manufactured parameters vanish. A block on which the six generators
of Eq. (d1-spans) all vanish,
```
  A Bᵀ = Dᵀ B = B + Bᵀ = 0, C Dᵀ = Cᵀ A = C + Cᵀ = 0,
```
is **terminal** (`IsTerminalBlock`): no move can move it. In particular a **Levi block**, one with
`B = C = 0`, is terminal (`isTerminalBlock_of_offDiag_zero`) — every one of the six products
involves `B` or `C`.

## Lemma D.3 (Two closed-form cases)

> **Lemma D.3.** Let `g = [[A, B], [C, D]] ∈ Sp(2w)`. If `C = 0`, then `S := Dᵀ B = A⁻¹ B` is
> symmetric, lies in `𝒮₊(g)`, and the single move `g ↦ g U_Z(S)` lands on a Levi block, which is
> terminal. Dually, if `B = 0`, then `T := Cᵀ A = Aᵀ C` is symmetric, lies in `𝒮₋(g)`, and the
> single move `g ↦ g L_X(T)` lands on a Levi block.

These are the *symbolic* rows of the local reduction (Lemma D.4): they dispatch, in a single move
and in closed form, every block with `C = 0` or `B = 0` (the `rank B = 0` / `rank C = 0` strata),
with no enumeration. The lemma is pure symplectic linear algebra — no code hypothesis — so it is
stated for an arbitrary symplectic `G = [[A, B], [C, D]] ∈ Sp(2n, 𝔽₂)` (the reduction applies it to
the cell blocks `g_cell ∈ Sp(2 w_cell)` of a code-preserving layer, and Lemma D.2 supplies the code
validity separately).

`S := Dᵀ B` is one of the three generators of `𝒮₊(g) = span {A Bᵀ, Dᵀ B, B + Bᵀ}`, so its
span-membership is immediate; symmetry is `(Dᵀ B)ᵀ = Bᵀ D = Dᵀ B` (Eq. (d1-sympl)); and the move
computes to a Levi block because `A S + B = (A Dᵀ) B + B = B + B = 0` using `A Dᵀ = 1` (the
off-diagonal symplectic relation with `C = 0`) and `S + S = 0` over `𝔽₂`. The identity `S = A⁻¹ B`
holds because `A Dᵀ = 1` makes `A` invertible with `Dᵀ = A⁻¹`; only `A Dᵀ = 1` is used below. The
`B = 0` case is dual under the `X ↔ Z` swap; there `D Aᵀ = 1` (the transpose of `A Dᵀ = 1`) gives
`C + D (Cᵀ A) = C + D (Aᵀ C) = C + (D Aᵀ) C = C + C = 0`.

No orthogonality `C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more".

## What is defined and proved

* `IsTerminalBlock` — Eq. (d1-term): the six-fold vanishing condition marking a terminal block.
* `isTerminalBlock_of_offDiag_zero` — a Levi block (`B = C = 0`) is terminal.
* `IsTerminalBlock.isSymm_B` / `IsTerminalBlock.isSymm_C` — the off-diagonal blocks `B`, `C` of a
  terminal block are symmetric (from the `B + Bᵀ = C + Cᵀ = 0` conjuncts, over `𝔽₂`); the reusable
  symmetry API consumed by the assembly and the reduction lemmas.
* `dragToLevi_of_lowerLeft_zero` — Lemma D.3, case `C = 0`: `S = Dᵀ B` is symmetric, lies in
  `𝒮₊(g) = span {A Bᵀ, Dᵀ B, B + Bᵀ}`, and `[[A, B], [0, D]] · U_Z(S) = [[A, 0], [0, D]]`, a Levi
  block (terminal by `isTerminalBlock_of_offDiag_zero`).
* `dragToLevi_of_upperRight_zero` — Lemma D.3, case `B = 0`: dually `T = Cᵀ A` is symmetric, lies in
  `𝒮₋(g) = span {C Dᵀ, Cᵀ A, C + Cᵀ}`, and `[[A, 0], [C, D]] · L_X(T) = [[A, 0], [0, D]]`.
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Terminal blocks (Eq. (d1-term)) -/

omit [DecidableEq ι] in
/-- **Eq. (d1-term): a terminal block.** A block `g = [[A, B], [C, D]]` is *terminal* when all six
generators of the two automatic-parameter spans `𝒮₊(g) = span {A Bᵀ, Dᵀ B, B + Bᵀ}`,
`𝒮₋(g) = span {C Dᵀ, Cᵀ A, C + Cᵀ}` (Eq. (d1-spans), Lemma D.2) vanish on it:
`A Bᵀ = Dᵀ B = B + Bᵀ = 0` and `C Dᵀ = Cᵀ A = C + Cᵀ = 0`. Every move is a left/right multiplication
by `U_Z(S)`/`L_X(T)` for a *nonzero* parameter in these spans, so a terminal block is fixed by every
move — it is "invisible to every possible move", the halting condition of the reduction walk. -/
def IsTerminalBlock (A B C D : Matrix ι ι (ZMod 2)) : Prop :=
  A * Bᵀ = 0 ∧ Dᵀ * B = 0 ∧ B + Bᵀ = 0 ∧ C * Dᵀ = 0 ∧ Cᵀ * A = 0 ∧ C + Cᵀ = 0

omit [DecidableEq ι] in
/-- **A Levi block is terminal.** A block with `B = C = 0` (a *Levi block*, `[[A, 0], [0, D]]`)
satisfies all six conditions of Eq. (d1-term): every generator is a product containing `B` or `C`,
or the symmetrization `B + Bᵀ` / `C + Cᵀ`, and vanishes when `B = C = 0`. This is the terminal
target that the two closed-form moves of Lemma D.3 land on. -/
theorem isTerminalBlock_of_offDiag_zero (A D : Matrix ι ι (ZMod 2)) :
    IsTerminalBlock A 0 0 D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

omit [DecidableEq ι] in
/-- **The upper-right block of a terminal block is symmetric.** Terminality includes `B + Bᵀ = 0`
(the third conjunct of Eq. (d1-term)), so `Bᵀ = -B = B` over `𝔽₂` (`neg_eq_self_zmod2`). The
accessor API used wherever a terminal block's diagonal-circuit parameter `B` must be symmetric to be
a genuine `Z`-shear (the assembly of §D.1, and the forthcoming reduction lemmas D.4–D.6). -/
theorem IsTerminalBlock.isSymm_B {A B C D : Matrix ι ι (ZMod 2)} (h : IsTerminalBlock A B C D) :
    B.IsSymm := by
  obtain ⟨_, _, hBBt, _, _, _⟩ := h
  rw [Matrix.IsSymm, eq_neg_of_add_eq_zero_right hBBt]
  exact neg_eq_self_zmod2 B

omit [DecidableEq ι] in
/-- **The lower-left block of a terminal block is symmetric** (dual to `IsTerminalBlock.isSymm_B`):
terminality includes `C + Cᵀ = 0` (the sixth conjunct of Eq. (d1-term)), so `Cᵀ = -C = C` over
`𝔽₂`. -/
theorem IsTerminalBlock.isSymm_C {A B C D : Matrix ι ι (ZMod 2)} (h : IsTerminalBlock A B C D) :
    C.IsSymm := by
  obtain ⟨_, _, _, _, _, hCCt⟩ := h
  rw [Matrix.IsSymm, eq_neg_of_add_eq_zero_right hCCt]
  exact neg_eq_self_zmod2 C

/-! ### Lemma D.3 (Two closed-form cases) -/

/-- **Lemma D.3, case `C = 0`.** For a symplectic block matrix `G = [[A, B], [0, D]] ∈ Sp(2n, 𝔽₂)`
(lower-left block zero), the parameter `S := Dᵀ B` is symmetric, lies in the upper
automatic-parameter span `𝒮₊(G) = span {A Bᵀ, Dᵀ B, B + Bᵀ}`, and the single right `Z`-shear move
`G ↦ G · U_Z(S)` lands on the Levi block `[[A, 0], [0, D]]` — which is terminal
(`isTerminalBlock_of_offDiag_zero`). Symmetry is `(Dᵀ B)ᵀ = Bᵀ D = Dᵀ B` (Eq. (d1-sympl)); the move
computes to `[[A, A S + B], [0, D]]` with `A S + B = (A Dᵀ) B + B = B + B = 0`, using the
off-diagonal symplectic relation `A Dᵀ = 1` (which, since `C = 0`, also exhibits
`S = Dᵀ B = A⁻¹ B`). -/
theorem dragToLevi_of_lowerLeft_zero {A B D : Matrix ι ι (ZMod 2)}
    (hsymp : Matrix.fromBlocks A B 0 D ∈ binarySymplecticGroup ι) :
    (Dᵀ * B).IsSymm ∧
      Dᵀ * B ∈ Submodule.span (ZMod 2) {A * Bᵀ, Dᵀ * B, B + Bᵀ} ∧
      Matrix.fromBlocks A B 0 D * shearZ (Dᵀ * B) = Matrix.fromBlocks A 0 0 D := by
  obtain ⟨_, _, _, hBtD, hADt, _⟩ := fromBlocks_symplectic_relations hsymp
  have hADt' : A * Dᵀ = 1 := by simpa using hADt
  refine ⟨?_, Submodule.subset_span (by simp), ?_⟩
  · change (Dᵀ * B)ᵀ = Dᵀ * B
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact hBtD
  · have hkey : A * (Dᵀ * B) + B = 0 := by
      rw [← Matrix.mul_assoc, hADt', Matrix.one_mul]
      exact Matrix.add_self_eq_zero B
    rw [shearZ, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [hkey]


/-- **Lemma D.3, case `B = 0`.** Dual to `dragToLevi_of_lowerLeft_zero` under the `X ↔ Z` swap: for
a symplectic block matrix `G = [[A, 0], [C, D]] ∈ Sp(2n, 𝔽₂)` (upper-right block zero), the
parameter `T := Cᵀ A` is symmetric, lies in the lower automatic-parameter span
`𝒮₋(G) = span {C Dᵀ, Cᵀ A, C + Cᵀ}`, and the single right `X`-shear move `G ↦ G · L_X(T)` lands on
the Levi block `[[A, 0], [0, D]]` — terminal by `isTerminalBlock_of_offDiag_zero`. Symmetry is
`(Cᵀ A)ᵀ = Aᵀ C = Cᵀ A` (Eq. (d1-sympl)); the move computes to `[[A, 0], [C + D T, D]]` with
`C + D T = C + D (Aᵀ C) = C + (D Aᵀ) C = C + C = 0`, using `D Aᵀ = 1` (the transpose of `A Dᵀ = 1`,
the off-diagonal symplectic relation with `B = 0`) and `T = Cᵀ A = Aᵀ C`. -/
theorem dragToLevi_of_upperRight_zero {A C D : Matrix ι ι (ZMod 2)}
    (hsymp : Matrix.fromBlocks A 0 C D ∈ binarySymplecticGroup ι) :
    (Cᵀ * A).IsSymm ∧
      Cᵀ * A ∈ Submodule.span (ZMod 2) {C * Dᵀ, Cᵀ * A, C + Cᵀ} ∧
      Matrix.fromBlocks A 0 C D * shearX (Cᵀ * A) = Matrix.fromBlocks A 0 0 D := by
  obtain ⟨_, _, hAtC, _, hADt, _⟩ := fromBlocks_symplectic_relations hsymp
  have hADt' : A * Dᵀ = 1 := by simpa using hADt
  have hDAt' : D * Aᵀ = 1 := by
    have h := congrArg Matrix.transpose hADt'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  refine ⟨?_, Submodule.subset_span (by simp), ?_⟩
  · change (Cᵀ * A)ᵀ = Cᵀ * A
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact hAtC
  · have hkey : C + D * (Cᵀ * A) = 0 := by
      rw [← hAtC, ← Matrix.mul_assoc, hDAt', Matrix.one_mul]
      exact Matrix.add_self_eq_zero C
    rw [shearX, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [hkey]

end CliffordCSS

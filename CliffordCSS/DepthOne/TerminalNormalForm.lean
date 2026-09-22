import CliffordCSS.DepthOne.TerminalFactor

/-!
# Terminal normal form — Lemma D.7 (Beyond transversality, App. D.1)

Pure mathematics : the **terminal normal form** classification
(Lemma D.7, `\label{lem:terminal}`) of the *reduction by multiplication* proof of the fixed-matching
generation theorem (Theorem D.1, `thm-depthone`) of *Beyond transversality* (arXiv:2608.05688).
Everything is `𝔽₂` symplectic linear algebra naming the raw carrier `Matrix`.

## The lemma (§D.1, Lemma "Terminal normal form", `lem:terminal`)

> Let `g = [[A, B], [C, D]]` be terminal, with local blocks. At width one, either `g = Id` or
> `g = U_Z(1) L_X(1) U_Z(1)`. At width two, either `B = C = 0`, in which case `g` is Levi, or
> `g = U_Z(B) L_X(C) U_Z(B)` with `B` and `C` symmetric.

`g` is a *single local block* `g_cell ∈ Sp(2 w_cell)` of a cell of width `w_cell ∈ {1, 2}`, so `A`,
`B`, `C`, `D` are the local `w_cell × w_cell` blocks. `terminal` is the six-fold vanishing predicate
`IsTerminalBlock` of Eq. (d1-term); a *Levi block* is one with `B = C = 0`;
and `U_Z(B) L_X(C) U_Z(B)` is the terminal `word`). The normal form is what
makes the canonical form of the reduction *factor* into valid depth-one layers.

## Relation to `terminalBlock_factor`

The assembly (`BeyondTransversalityTerminalFactor.lean`, PR #83) reaches the factorization
`G_term = [[A + BC, 0], [0, D + CB]] · W` (Eq. (d1-factor), `terminalBlock_factor`) *directly and
globally*, deliberately **bypassing** this per-cell rank classification. That global route suffices
for Theorem D.1's assembly but does not itself formalize the paper's Lemma D.7 statement — the
explicit width-one / width-two normal forms. This file formalizes that actual statement, giving the
faithful normal-form classification the lemma asserts (grounding it in the real width-one/width-two
theorems rather than in the factorization proxy).

## What is proved here (both widths + the reusable Levi branch)

* `scalar_terminal_symplectic_cases` — the underlying `𝔽₂` scalar fact: for scalars `a, b, c, d` the
  width-one terminal conditions (`a b = d b = c d = c a = 0`) together with the symplectic relation
  `a d + b c = 1` force `(a, b, c, d) = (1, 0, 0, 1)` (identity) or `(0, 1, 1, 0)` (the swap). A
  16-case kernel `decide`.
* `terminalNormalForm_width_one` — **Lemma D.7, width one.** For a terminal symplectic block over a
  one-element index type (`Unique ι`, i.e. `w = 1`), `g = Id` or `g = U_Z(1) L_X(1) U_Z(1)`
  (`= word 1 1 = [[0, 1], [1, 0]]`). Proved by reducing every matrix condition to its single entry
  (`Fintype.sum_unique`) and applying `scalar_terminal_symplectic_cases`.
* `levi_of_mul_offDiag_zero` — **Case (i) of the width-two classification, at every width.** A
  terminal symplectic block with `B C = 0` is Levi (`B = C = 0`). This is the paper's "Case (i):
  `B = 0` or `C = 0`" made general: from `B C = 0` the symplectic relation `A Dᵀ + B C = I` gives
  `A Dᵀ = I`, so `A` is invertible, and terminality's `A B = 0`, `C A = 0` (via `B`, `C` symmetric)
  force `B = C = 0`. The Levi branch the width-two case consumes.
* `projection_bimodule_eq` — the `2 × 2` `𝔽₂` linear-algebra core of the non-Levi width-two case: a
  nonzero matrix `A` fixed on both sides by a non-identity idempotent `P` (`A P = A = P A`,
  `P² = P`, `P ≠ I`) equals `P`, because such a `P` has rank `≤ 1` and its bimodule `End(im P)` is
  one-dimensional. A `16 × 16`-pair kernel `decide`.
* `terminalNormalForm_width_two` — **Lemma D.7, width two.** A terminal symplectic block over a
  two-element index type (`Fin 2`, i.e. `w = 2`) is either Levi (`B = C = 0`) or equals the terminal
  word `word B C = U_Z(B) L_X(C) U_Z(B)`, with `B`, `C` symmetric. The non-Levi case (`B C ≠ 0`,
  Cases (ii)/(iii)) is handled uniformly: `B C B = B` and `C B C = C` fall out of the symplectic
  relation, making `I + B C` and `I + C B` idempotents `≠ I`, and `projection_bimodule_eq` then pins
  `A = I + B C`, `D = I + C B`, so `g = [[I+BC, BCB], [C, I+CB]] = word B C` (Eq. (d1-antidiag)).

Together with `terminalNormalForm_width_one` this is the complete Lemma D.7 (Terminal normal form).

No orthogonality `C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more".
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The `𝔽₂` scalar classification (width-one core) -/

/-- **The width-one terminal-symplectic scalar cases.** For scalars `a, b, c, d ∈ 𝔽₂`, the four
width-one terminal conditions `a b = 0`, `d b = 0`, `c d = 0`, `c a = 0` (Eq. (d1-term) at `w = 1`,
the two symmetry conditions being vacuous) together with the symplectic relation `a d + b c = 1`
(Eq. (d1-sympl)) leave exactly two solutions: `(a, b, c, d) = (1, 0, 0, 1)` — the identity — and
`(a, b, c, d) = (0, 1, 1, 0)` — the swap `[[0, 1], [1, 0]] = U_Z(1) L_X(1) U_Z(1)`. Verified by
exhausting the `16` value assignments with a kernel `decide`. -/
theorem scalar_terminal_symplectic_cases :
    ∀ a b c d : ZMod 2, a * b = 0 → d * b = 0 → c * d = 0 → c * a = 0 → a * d + b * c = 1 →
      (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by decide

/-! ### Lemma D.7, width one -/

/-- **Lemma D.7, width one.** A terminal symplectic block `g = [[A, B], [C, D]] ∈ Sp(2, 𝔽₂)` over a
one-element index type (`Unique ι`, i.e. a width-one cell) is either the identity or the swap
`U_Z(1) L_X(1) U_Z(1) = word 1 1 = [[0, 1], [1, 0]]`.

At width one every block is a `1 × 1` scalar, so each matrix condition reduces to its single entry
(`Fintype.sum_unique` for products, `Matrix.transpose` acting trivially): terminality gives
`a b = d b = c d = c a = 0` and the symplectic relation gives `a d + b c = 1`, whence
`scalar_terminal_symplectic_cases` forces `(a, b, c, d) ∈ {(1,0,0,1), (0,1,1,0)}`. Reassembling the
entries gives `g = Id` (`fromBlocks 1 0 0 1`) or `g = word 1 1` (`fromBlocks 0 1 1 0`), the two
terminal blocks of `Sp(2)`. -/
theorem terminalNormalForm_width_one [Unique ι]
    {A B C D : Matrix ι ι (ZMod 2)}
    (hsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι)
    (hterm : IsTerminalBlock A B C D) :
    Matrix.fromBlocks A B C D = 1 ∨ Matrix.fromBlocks A B C D = word 1 1 := by
  -- entry of a product / transpose / matrix over a one-element index type
  have hAd : ∀ M N : Matrix ι ι (ZMod 2),
      (M * N) default default = M default default * N default default :=
    fun M N => by rw [Matrix.mul_apply, Fintype.sum_unique]
  have hTd : ∀ M : Matrix ι ι (ZMod 2), Mᵀ default default = M default default := fun _ => rfl
  have mk_one : ∀ M : Matrix ι ι (ZMod 2), M default default = 1 → M = 1 := by
    intro M h; ext i j
    rw [Unique.eq_default i, Unique.eq_default j, Matrix.one_apply_eq]; exact h
  have mk_zero : ∀ M : Matrix ι ι (ZMod 2), M default default = 0 → M = 0 := by
    intro M h; ext i j
    rw [Unique.eq_default i, Unique.eq_default j, Matrix.zero_apply]; exact h
  obtain ⟨hABt, hDtB, _, hCDt, hCtA, _⟩ := hterm
  obtain ⟨_, _, _, _, h5, _⟩ := fromBlocks_symplectic_relations hsymp
  -- reduce every block condition to its single scalar entry
  have e_ab : A default default * B default default = 0 := by
    have h := congrFun (congrFun hABt default) default; rwa [hAd, hTd, Matrix.zero_apply] at h
  have e_db : D default default * B default default = 0 := by
    have h := congrFun (congrFun hDtB default) default; rwa [hAd, hTd, Matrix.zero_apply] at h
  have e_cd : C default default * D default default = 0 := by
    have h := congrFun (congrFun hCDt default) default; rwa [hAd, hTd, Matrix.zero_apply] at h
  have e_ca : C default default * A default default = 0 := by
    have h := congrFun (congrFun hCtA default) default; rwa [hAd, hTd, Matrix.zero_apply] at h
  have e_symp :
      A default default * D default default + B default default * C default default = 1 := by
    have h := congrFun (congrFun h5 default) default
    rw [Matrix.add_apply, hAd, hAd, hTd, hTd, Matrix.one_apply_eq] at h; exact h
  rcases scalar_terminal_symplectic_cases _ _ _ _ e_ab e_db e_cd e_ca e_symp with
    ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · left
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    exact ⟨mk_one A ha, mk_zero B hb, mk_zero C hc, mk_one D hd⟩
  · right
    rw [word_one_one, symplecticMatrix, Matrix.fromBlocks_inj]
    exact ⟨mk_zero A ha, mk_one B hb, mk_one C hc, mk_zero D hd⟩

/-! ### Case (i) of the width-two classification, at every width -/

/-- **The Levi branch of the terminal normal form (Case (i)), general width.** A terminal symplectic
block `g = [[A, B], [C, D]]` whose off-diagonal product `B C` vanishes is a *Levi block*: `B = 0`
and `C = 0`.

This is the paper's "Case (i): `B = 0` or `C = 0`" freed of the width-two restriction. From
terminality `B`, `C` are symmetric (`IsTerminalBlock.isSymm_B/C`), so `B Cᵀ = B C`; the symplectic
relation `A Dᵀ + B Cᵀ = I` (Eq. (d1-sympl)) then reads `A Dᵀ = I` once `B C = 0`, making `A`
invertible with `Dᵀ` as inverse (`mul_eq_one_comm`). Terminality also gives `A B = 0` and `C A = 0`
(from `A Bᵀ = 0`, `Cᵀ A = 0` with `B`, `C` symmetric); left/right cancelling by `Dᵀ A = I` /
`A Dᵀ = I` forces `B = 0`, `C = 0`. The width-two case consumes this for its `B C = 0` sub-case. -/
theorem levi_of_mul_offDiag_zero {A B C D : Matrix ι ι (ZMod 2)}
    (hsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup ι)
    (hterm : IsTerminalBlock A B C D) (hbc : B * C = 0) :
    B = 0 ∧ C = 0 := by
  have hBsymm : Bᵀ = B := hterm.isSymm_B
  have hCsymm : Cᵀ = C := hterm.isSymm_C
  obtain ⟨hABt, _, _, _, hCtA, _⟩ := hterm
  have hAB : A * B = 0 := by rw [← hBsymm]; exact hABt
  have hCA : C * A = 0 := by rw [← hCsymm]; exact hCtA
  obtain ⟨_, _, _, _, h5, _⟩ := fromBlocks_symplectic_relations hsymp
  rw [hCsymm] at h5
  have hADt : A * Dᵀ = 1 := by rw [hbc, add_zero] at h5; exact h5
  have hDtA : Dᵀ * A = 1 := mul_eq_one_comm.mp hADt
  refine ⟨?_, ?_⟩
  · have h : Dᵀ * (A * B) = 0 := by rw [hAB, Matrix.mul_zero]
    rwa [← Matrix.mul_assoc, hDtA, Matrix.one_mul] at h
  · have h : (C * A) * Dᵀ = 0 := by rw [hCA, Matrix.zero_mul]
    rwa [Matrix.mul_assoc, hADt, Matrix.mul_one] at h

/-! ### Cases (ii)/(iii): the non-Levi width-two normal form -/

set_option maxRecDepth 4000 in
/-- **A rank-`≤ 1` idempotent's bimodule is one-dimensional (`𝔽₂`, `2 × 2`).** If `P` is an
idempotent `2 × 2` matrix over `𝔽₂` that is not the identity (`P ≠ 1`, so `P` has rank `≤ 1`) and
`A` is a nonzero matrix fixed by `P` on both sides (`A P = A`, `P A = A`), then `A = P`. The fixed
set `{X : P X = X ∧ X P = X}` is `End(im P)`, of dimension `(rank P)² ≤ 1`; being nonzero, `A` spans
it together with `P`, forcing `A = P`. Verified by exhausting the `16 × 16` pairs `(A, P)` with a
kernel `decide`. This is the linear-algebraic core of the non-Levi width-two terminal normal form
(Cases (ii)/(iii) of Lemma D.7): applied to the idempotents `I + BC`, `I + CB` it pins the diagonal
blocks `A = I + BC`, `D = I + CB`. -/
theorem projection_bimodule_eq {A P : Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (hPP : P * P = P) (hP1 : P ≠ 1) (hA0 : A ≠ 0)
    (hAP : A * P = A) (hPA : P * A = A) : A = P := by
  revert hPP hP1 hA0 hAP hPA; revert A P; decide

/-- **Lemma D.7, width two.** A terminal symplectic block `g = [[A, B], [C, D]] ∈ Sp(4, 𝔽₂)` over a
two-element index type (`Fin 2`, i.e. a width-two cell) is either Levi (`B = 0 ∧ C = 0`) or equals
the terminal word `word B C = U_Z(B) L_X(C) U_Z(B)`, with `B` and `C` symmetric.

Terminality gives `B`, `C` symmetric (`IsTerminalBlock.isSymm_B/C`) and, once symmetry is folded in,
the block relations `A B = 0`, `C A = 0`, `Dᵀ B = 0`, `C Dᵀ = 0` (and `B D = 0`, `D C = 0` by
transposition); symplecticity gives `A Dᵀ = I + B C` and `Aᵀ D = I + C B` (Eq. (d1-sympl)). When
`B C = 0` the block is Levi (`levi_of_mul_offDiag_zero`, the paper's Case (i)). Otherwise `B C ≠ 0`,
covering Cases (ii)/(iii) uniformly: multiplying the symplectic relation `A Dᵀ + B C = I` on the
right by `B` (using `Dᵀ B = 0`) gives `B C B = B`, and on the left by `C` (using `C A = 0`) gives
`C B C = C`. Hence `I + B C` and `I + C B` are idempotents `≠ I`, and — since `A B = 0`, `C A = 0`
make `A` fixed by `I + B C` on both sides (dually for `D`) while `A ≠ 0` (from `A Dᵀ = I + B C ≠ 0`)
— `projection_bimodule_eq` forces `A = I + B C` and `D = I + C B`. With `B C B = B` this gives
`g = [[I+BC, B], [C, I+CB]] = [[I+BC, BCB], [C, I+CB]] = word B C` (Eq. (d1-antidiag)). No
orthogonality `C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more". -/
theorem terminalNormalForm_width_two {A B C D : Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (hsymp : Matrix.fromBlocks A B C D ∈ binarySymplecticGroup (Fin 2))
    (hterm : IsTerminalBlock A B C D) :
    (B = 0 ∧ C = 0) ∨
      (Matrix.fromBlocks A B C D = word B C ∧ B.IsSymm ∧ C.IsSymm) := by
  by_cases hBC : B * C = 0
  · exact Or.inl (levi_of_mul_offDiag_zero hsymp hterm hBC)
  · refine Or.inr ⟨?_, hterm.isSymm_B, hterm.isSymm_C⟩
    have hBsymm : Bᵀ = B := hterm.isSymm_B
    have hCsymm : Cᵀ = C := hterm.isSymm_C
    obtain ⟨hABt, hDtB, _, hCDt, hCtA, _⟩ := hterm
    obtain ⟨_, _, _, _, hr5, hr6⟩ := fromBlocks_symplectic_relations hsymp
    have hAB : A * B = 0 := by rw [← hBsymm]; exact hABt
    have hCA : C * A = 0 := by rw [← hCsymm]; exact hCtA
    rw [hCsymm] at hr5 hr6
    -- the two off-diagonal terminality products, transposed into `B`- and `C`-right form
    have hBD : B * D = 0 := by
      have h := congrArg Matrix.transpose hDtB
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
        hBsymm] at h
    have hDC : D * C = 0 := by
      have h := congrArg Matrix.transpose hCDt
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
        hCsymm] at h
    -- `B C B = B` and `C B C = C` from the symplectic relation `A Dᵀ + B C = I`
    have hBCB : B * C * B = B := by
      have h : (A * Dᵀ + B * C) * B = B := by rw [hr5, Matrix.one_mul]
      rwa [add_mul, Matrix.mul_assoc A Dᵀ B, hDtB, Matrix.mul_zero, zero_add] at h
    have hCBC : C * B * C = C := by
      have h : C * (A * Dᵀ + B * C) = C := by rw [hr5, Matrix.mul_one]
      rw [Matrix.mul_add, ← Matrix.mul_assoc C A Dᵀ, hCA, Matrix.zero_mul, zero_add] at h
      rw [Matrix.mul_assoc]; exact h
    -- `I + B C` and `I + C B` are idempotent
    have hee : (B * C) * (B * C) = B * C := by
      rw [Matrix.mul_assoc B C (B * C), ← Matrix.mul_assoc C B C, hCBC]
    have hff : (C * B) * (C * B) = C * B := by
      rw [Matrix.mul_assoc C B (C * B), ← Matrix.mul_assoc B C B, hBCB]
    have hPP : (1 + B * C) * (1 + B * C) = 1 + B * C := by
      rw [add_mul, one_mul, mul_add, Matrix.mul_one, hee, Matrix.add_self_eq_zero, add_zero]
    have hQQ : (1 + C * B) * (1 + C * B) = 1 + C * B := by
      rw [add_mul, one_mul, mul_add, Matrix.mul_one, hff, Matrix.add_self_eq_zero, add_zero]
    -- `A` is fixed by `I + B C` on both sides (dually `D` by `I + C B`)
    have hAPeq : A * (1 + B * C) = A := by
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hAB, Matrix.zero_mul, add_zero]
    have hPAeq : (1 + B * C) * A = A := by
      rw [add_mul, one_mul, Matrix.mul_assoc, hCA, Matrix.mul_zero, add_zero]
    have hDQeq : D * (1 + C * B) = D := by
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hDC, Matrix.zero_mul, add_zero]
    have hQDeq : (1 + C * B) * D = D := by
      rw [add_mul, one_mul, Matrix.mul_assoc, hBD, Matrix.mul_zero, add_zero]
    -- the idempotents are not the identity (`B C = 0` was the excluded Levi case)
    have hPne1 : (1 + B * C) ≠ 1 := by
      intro h; apply hBC
      have h2 : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + B * C = 1 + 0 := by
        rw [add_zero]; exact h
      exact add_left_cancel h2
    have hQne1 : (1 + C * B) ≠ 1 := by
      intro h
      have hCB0 : C * B = 0 := by
        have h2 : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + C * B = 1 + 0 := by
          rw [add_zero]; exact h
        exact add_left_cancel h2
      have hB0 : B = 0 := by
        have hb : B * (C * B) = B := by rw [← Matrix.mul_assoc]; exact hBCB
        rw [hCB0, Matrix.mul_zero] at hb; exact hb.symm
      exact hBC (by rw [hB0, Matrix.zero_mul])
    -- `A Dᵀ = I + B C` and `Aᵀ D = I + C B` (symplectic relations, `-x = x` over `𝔽₂`)
    have hADt : A * Dᵀ = 1 + B * C := by
      have h : A * Dᵀ = 1 - B * C := eq_sub_of_add_eq hr5
      rwa [sub_eq_add_neg, neg_eq_self_zmod2] at h
    have hAtD : Aᵀ * D = 1 + C * B := by
      have h : Aᵀ * D = 1 - C * B := eq_sub_of_add_eq hr6
      rwa [sub_eq_add_neg, neg_eq_self_zmod2] at h
    -- pin the diagonal blocks
    have hAeqP : A = 1 + B * C := by
      by_cases hA0 : A = 0
      · rw [hA0]; rw [hA0, Matrix.zero_mul] at hADt; exact hADt
      · exact projection_bimodule_eq hPP hPne1 hA0 hAPeq hPAeq
    have hDeqQ : D = 1 + C * B := by
      by_cases hD0 : D = 0
      · rw [hD0]; rw [hD0, Matrix.mul_zero] at hAtD; exact hAtD
      · exact projection_bimodule_eq hQQ hQne1 hD0 hDQeq hQDeq
    -- reassemble `g = word B C`
    rw [word_eq_fromBlocks, Matrix.fromBlocks_inj]
    exact ⟨hAeqP, hBCB.symm, rfl, hDeqQ⟩

end CliffordCSS

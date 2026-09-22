import CliffordCSS.DepthOne.GlobalReduction
import CliffordCSS.DepthOne.LocalReductionTwo

/-!
# Theorem D.1 (Fixed-matching generation) and Lemma D.6, unconditional

Pure mathematics . This file **discharges the single remaining
hypothesis** of the two headline results of Appendix D.1 of *Beyond transversality*
(arXiv:2608.05688), turning the *conditional* forms proved in
`BeyondTransversalityGlobalReduction.lean` into the paper's actual statements.

The hypothesis was the width-two half of **Lemma D.4 (Local reduction)**, `LocalReduction 2 3`
("every element of `Sp(4, 𝔽₂)` reaches a terminal block in at most three moves"). It is now a
theorem — `localReduction_width_two` (`BeyondTransversalityLocalReductionTwo.lean`), proved in the
kernel by the packed reverse-reachability route (generator-closure completeness of `Sp(4, 𝔽₂)`
plus a bounded-reachability `decide`, no `native_decide`). Feeding it to the conditional results
removes the hypothesis:

* `exists_terminalLayer` — **Lemma D.6 (Global reduction)**, unconditional.
* `fixedMatchingSlice_eq_sup_familyM` — **Theorem D.1**, unconditional (Eq. (D3)):
  `N_M = ⟨ S^Z_M, S^X_M, L_M ⟩` as the subgroup equality
  `fixedMatchingSlice = shearZFamilyM ⊔ shearXFamilyM ⊔ leviFamilyM`, where the `⊔` join of the
  three (sub)group families *is* the subgroup they generate.

Neither result now carries a `LocalReduction` hypothesis, and neither is a weakening of the
paper: both are stated at the paper's full generality (arbitrary CSS-form label space `(C_X, C_Z)`
and arbitrary matching `σ`, `σ² = 1`; orthogonality `C_X ⊥ C_Z` is not used). -/

open Matrix

namespace CliffordCSS

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)} {σ : Equiv.Perm ι}

/-- **Lemma D.6 (Global reduction).** Every `G ∈ N_M` can be carried to a layer `G_term ∈ N_M` all
of whose cell blocks are terminal, by left and right multiplication with elements of `S^Z_M` and
`S^X_M`; **at most `m₁ + 3 m₂` such multiplications are required** (`m₁`, `m₂` the numbers of cells
of width one and two). The two multiplication words `L`, `R` are returned explicitly as lists of
family elements, so their total length *is* the number of multiplications performed, and terminality
is delivered both blockwise and as terminality of the whole layer.

This is `exists_terminalLayer_of_localReduction` with its `LocalReduction 2 3` hypothesis discharged
by `localReduction_width_two`; the width-one half is the already-proved `localReduction_width_one`.
The lemma is therefore now **unconditional**. -/
theorem exists_terminalLayer (hσ : Function.Involutive σ) {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ fixedMatchingSlice C_X C_Z σ hσ) :
    ∃ L R : List ↥(binarySymplecticGroup ι),
      IsShearWordM C_X C_Z σ hσ L ∧ IsShearWordM C_X C_Z σ hσ R ∧
      L.length + R.length ≤ (singletonCells σ).card + 3 * (pairCells σ).card ∧
      L.prod * G * R.prod ∈ fixedMatchingSlice C_X C_Z σ hσ ∧
      (∀ b ∈ matchingCells σ, IsTerminalLayer (localBlock b
        ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)))) ∧
      IsTerminalLayer
        ((L.prod * G * R.prod : ↥(binarySymplecticGroup ι)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) :=
  exists_terminalLayer_of_localReduction localReduction_width_two hσ hG

/-- **Theorem D.1 (Fixed-matching generation), Eq. (D3).** For every CSS-form label space and every
matching `M`,
`N_M = ⟨ S^Z_M, S^X_M, L_M ⟩ = S^Z_M ⊔ S^X_M ⊔ L_M` — *unconditionally*. The `⊇` inclusion is the
easy `sup_familyM_le_fixedMatchingSlice`; the `⊆` inclusion is the reduction-by-multiplication of
Lemma D.6 (`exists_terminalLayer`) followed by the terminal factorization
(`terminalLayer_mem_sup_familyM`, Eq. (d1-factor)), with `G = L.prod⁻¹ (L.prod G R.prod) R.prod⁻¹`
exhibiting `G` as a word in the three families.

This is `fixedMatchingSlice_eq_sup_familyM_of_localReduction` with its `LocalReduction 2 3`
hypothesis discharged by `localReduction_width_two`. It is the paper's Theorem D.1 itself, no longer
the implication `LocalReduction 2 3 → Theorem D.1`, and it is stated at the paper's full generality
(orthogonality `C_X ⊥ C_Z` is not assumed). -/
theorem fixedMatchingSlice_eq_sup_familyM (hσ : Function.Involutive σ) :
    fixedMatchingSlice C_X C_Z σ hσ
      = shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ ⊔ leviFamilyM C_X C_Z σ hσ :=
  fixedMatchingSlice_eq_sup_familyM_of_localReduction localReduction_width_two hσ

end CliffordCSS

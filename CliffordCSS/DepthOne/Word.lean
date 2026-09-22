import CliffordCSS.DepthOne.AutoParams

/-!
# The terminal word `W = U_Z(B) L_X(C) U_Z(B)` and its involution
(Beyond transversality, App. D.1 — the assembly identities Eq. (d1-W)/(d1-antidiag))

Pure mathematics : the **terminal word** `W = U_Z(B) L_X(C) U_Z(B)`
of the *reduction by multiplication* proof of the fixed-matching generation theorem (Theorem D.1,
`thm-depthone`) of *Beyond transversality* (arXiv:2608.05688), and the three facts about it that the
final assembly (§D.1, "Terminal layers factor") uses. Everything is `𝔽₂` symplectic linear algebra
naming the raw carrier `Matrix`.

## The word `W` (Eq. (d1-W), Eq. (d1-antidiag))

In the assembly, a blockwise-terminal layer `G_term = [[A, B], [C, D]]` (all six parameters of
Lemma D.2 vanishing) has `B`, `C` symmetric, so `U_Z(B)` and `L_X(C)` are genuine diagonal circuits.
The paper forms the **word**
```
  W := U_Z(B) · L_X(C) · U_Z(B)
```
and computes it in closed form (Eq. (d1-W)):
```
  W = [[I + B C, B C B], [C, I + C B]].
```
Two of its properties drive the assembly, and neither needs a hypothesis on `B`, `C`:

* **`W` is an involution** (`word_mul_self`): `W W = I`. Because each `Z`- and `X`-shear is its own
  inverse over `𝔽₂` (`shearZ_mul_self`, `shearX_mul_self`) and `W` is the palindrome
  `U_Z(B) L_X(C) U_Z(B)`, we get `W W = U_Z(B) L_X(C) (U_Z(B) U_Z(B)) L_X(C) U_Z(B) =
  U_Z(B) (L_X(C) L_X(C)) U_Z(B) = U_Z(B) U_Z(B) = I`. Hence `W⁻¹ = W`, and the assembly's
  `L* = G_term W⁻¹ = G_term W` needs no inverse.
* **the block form** `word_eq_fromBlocks` (Eq. (d1-W)/(d1-antidiag)), the pure `fromBlocks_multiply`
  computation `(I + B C) B + B = B C B` (using `B + B = 0`) for the top-right block.

When `B`, `C` are additionally symmetric, `W` is symplectic (`word_mem_binarySymplecticGroup`); when
`B`, `C` are `M`-block-diagonal, so is `W` (`word_isSpBlockDiagonal`); and when `B`, `C` are the
admissible, `M`-block-diagonal parameters of the two families (as terminality + validity supply),
`W ∈ ⟨S^Z_M, S^X_M⟩` (`word_mem_sup_shearFamilyM`) — each of its three factors is a generator, so
the word lies in the generated subgroup. These are exactly the memberships the reverse inclusion of
Theorem D.1 rearranges into a group word.

No orthogonality `C_X ⊥ C_Z` is used — "a statement about split subspaces and nothing more".

## What is defined and proved

* `word` — the word `W = U_Z(B) L_X(C) U_Z(B)` as a `2n × 2n` matrix over `𝔽₂`.
* `shearZ_mul_shearX` — the intermediate product `U_Z(B) L_X(C) = [[I + B C, B], [C, I]]`.
* `word_eq_fromBlocks` — Eq. (d1-W)/(d1-antidiag): `W = [[I + B C, B C B], [C, I + C B]]`.
* `word_one_one` — the "swap" specialization `W(I, I) = [[0, I], [I, 0]] = symplecticMatrix`.
* `word_mul_self` — `W` is an involution, `W W = I` (no hypothesis).
* `word_mem_binarySymplecticGroup` — for symmetric `B`, `C`, `W` is symplectic.
* `word_isSpBlockDiagonal` — for `M`-block-diagonal `B`, `C`, `W` is `M`-block-diagonal.
* `word_mem_sup_shearFamilyM` — for admissible `M`-block-diagonal `B ∈ S^Z_M`-parameters,
  `C ∈ S^X_M`-parameters, `W ∈ S^Z_M ⊔ S^X_M` (the join of the two diagonal families).
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The word `W = U_Z(B) L_X(C) U_Z(B)` and its block form (Eq. (d1-W)) -/

/-- The **terminal word** `W = U_Z(B) · L_X(C) · U_Z(B)` of the assembly step of Theorem D.1
(§D.1, Eq. (d1-W)): the product of the two `Z`-shears `U_Z(B) = [[I, B], [0, I]]` sandwiching the
`X`-shear `L_X(C) = [[I, 0], [C, I]]`. For a blockwise-terminal layer `[[A, B], [C, D]]` with `B`,
`C` symmetric it equals that layer's `Word`-part; in general it is the closed form
`[[I + B C, B C B], [C, I + C B]]` (`word_eq_fromBlocks`). -/
def word (B C : Matrix ι ι (ZMod 2)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  shearZ B * shearX C * shearZ B

/-- The intermediate product `U_Z(B) L_X(C) = [[I + B C, B], [C, I]]`: multiplying
`[[I, B], [0, I]]` by `[[I, 0], [C, I]]` via `fromBlocks_multiply`. -/
theorem shearZ_mul_shearX (B C : Matrix ι ι (ZMod 2)) :
    shearZ B * shearX C = Matrix.fromBlocks (1 + B * C) B C 1 := by
  rw [shearZ, shearX, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, zero_add]

/-- **Eq. (d1-W)/(d1-antidiag): the block form of the word.** `W = U_Z(B) L_X(C) U_Z(B) =
[[I + B C, B C B], [C, I + C B]]`. Computed by `shearZ_mul_shearX` followed by one more
`fromBlocks_multiply`; the only non-trivial block is the top-right `(I + B C) B + B = B C B`, which
uses `B + B = 0` over `𝔽₂`. No hypothesis on `B`, `C` is needed — this is a matrix identity. -/
theorem word_eq_fromBlocks (B C : Matrix ι ι (ZMod 2)) :
    word B C = Matrix.fromBlocks (1 + B * C) (B * C * B) C (1 + C * B) := by
  have hBB : B + B = 0 := Matrix.add_self_eq_zero B
  rw [word, shearZ_mul_shearX, shearZ, Matrix.fromBlocks_multiply]
  have htr : (1 + B * C) * B + B * 1 = B * C * B := by
    rw [Matrix.mul_one, add_mul, Matrix.one_mul, add_right_comm, hBB, zero_add]
  have hbr : C * B + 1 * 1 = 1 + C * B := by rw [Matrix.one_mul, add_comm]
  rw [Matrix.mul_one, Matrix.mul_zero, add_zero, htr]
  rw [Matrix.mul_one, Matrix.mul_zero, add_zero, hbr]

/-- **The word at the identity parameters is the Gram matrix**:
`W = U_Z(I) L_X(I) U_Z(I) = [[0, I], [I, 0]] = symplecticMatrix`. Specializing
`word_eq_fromBlocks` at `B = C = I` gives `[[I + I, I], [I, I + I]]`, and `I + I = 0` over `𝔽₂`
(`Matrix.add_self_eq_zero`). This is the "swap" block: the second terminal block of `Sp(2, 𝔽₂)` at
width one, and the anti-diagonal matrix `Λ` of Nielsen & Chuang eq. (10.84) already named
`CliffordCSS.symplecticMatrix`. -/
theorem word_one_one : word (1 : Matrix ι ι (ZMod 2)) 1 = symplecticMatrix := by
  rw [word_eq_fromBlocks, mul_one, mul_one, Matrix.add_self_eq_zero, symplecticMatrix]

/-! ### `W` is an involution (Eq. (d1-W) remark) -/

/-- **The word is an involution:** `W W = I`. Each shear is its own inverse over `𝔽₂`
(`shearZ_mul_self`, `shearX_mul_self`) and `W = U_Z(B) L_X(C) U_Z(B)` is a palindrome, so the two
central `U_Z(B)`'s cancel, then the two `L_X(C)`'s, then the two outer `U_Z(B)`'s. Hence `W⁻¹ = W`,
which is why the assembly's `L* = G_term W⁻¹ = G_term W` needs no inverse. -/
theorem word_mul_self (B C : Matrix ι ι (ZMod 2)) : word B C * word B C = 1 := by
  simp only [word, mul_assoc]
  rw [← mul_assoc (shearZ B) (shearZ B), shearZ_mul_self, one_mul,
    ← mul_assoc (shearX C) (shearX C), shearX_mul_self, one_mul, shearZ_mul_self]

/-! ### Symplecticity, block-diagonality, and family membership -/

/-- **`W` is symplectic for symmetric parameters.** When `B` and `C` are symmetric, `U_Z(B)` and
`L_X(C)` are symplectic (`shearZ_mem_iff`, `shearX_mem_iff`), so their product `W` lies in
`Sp(2n, 𝔽₂)`. -/
theorem word_mem_binarySymplecticGroup {B C : Matrix ι ι (ZMod 2)}
    (hB : B.IsSymm) (hC : C.IsSymm) : word B C ∈ binarySymplecticGroup ι := by
  rw [word]
  exact mul_mem (mul_mem (shearZ_mem_iff.mpr hB) (shearX_mem_iff.mpr hC)) (shearZ_mem_iff.mpr hB)

/-- **`W` is `M`-block-diagonal for `M`-block-diagonal parameters.** When `B` and `C` are
`M`-block-diagonal (`IsCellDiagonal σ`), each of `U_Z(B)`, `L_X(C)` is `M`-block-diagonal (their
four blocks are `I`, `B`/`C`, `0`, `I`), and the product of `M`-block-diagonal symplectic
matrices is `M`-block-diagonal (`isSpBlockDiagonal_mul`, using `σ² = id`). -/
theorem word_isSpBlockDiagonal {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    {B C : Matrix ι ι (ZMod 2)} (hB : IsCellDiagonal σ B) (hC : IsCellDiagonal σ C) :
    IsSpBlockDiagonal σ (word B C) := by
  rw [word]
  exact isSpBlockDiagonal_mul hσ
    (isSpBlockDiagonal_mul hσ (shearZ_isSpBlockDiagonal hB) (shearX_isSpBlockDiagonal hC))
    (shearZ_isSpBlockDiagonal hB)

/-- **The word lies in `⟨S^Z_M, S^X_M⟩`.** For admissible, `M`-block-diagonal parameters
`B ∈ admissibleParamsBlockDiag C_X C_Z σ` (so `U_Z(B) ∈ S^Z_M`) and
`C ∈ admissibleParamsBlockDiag C_Z C_X σ` (so `L_X(C) ∈ S^X_M`), any symplectic-group element `G`
with `↑G = W = U_Z(B) L_X(C) U_Z(B)` lies in the join `S^Z_M ⊔ S^X_M`: it is a product of the three
generators `U_Z(B) ∈ S^Z_M`, `L_X(C) ∈ S^X_M`, `U_Z(B) ∈ S^Z_M`, each in the join. This is the
membership the reverse inclusion of Theorem D.1 uses for the `Word`-part of a terminal layer. -/
theorem word_mem_sup_shearFamilyM {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)} {σ : Equiv.Perm ι}
    (hσ : Function.Involutive σ) {B C : Matrix ι ι (ZMod 2)}
    (hB : B ∈ admissibleParamsBlockDiag C_X C_Z σ)
    (hC : C ∈ admissibleParamsBlockDiag C_Z C_X σ) {G : ↥(binarySymplecticGroup ι)}
    (hG : (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = word B C) :
    G ∈ shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ := by
  obtain ⟨hBsymm, _, _⟩ := mem_admissibleParamsBlockDiag.mp hB
  obtain ⟨hCsymm, _, _⟩ := mem_admissibleParamsBlockDiag.mp hC
  let uB : ↥(binarySymplecticGroup ι) := ⟨shearZ B, shearZ_mem_iff.mpr hBsymm⟩
  let lC : ↥(binarySymplecticGroup ι) := ⟨shearX C, shearX_mem_iff.mpr hCsymm⟩
  have hGeq : G = uB * lC * uB := by
    apply Subtype.ext
    rw [hG, word]
    rfl
  have h1 : uB ∈ shearZFamilyM C_X C_Z σ hσ := shearZ_mem_shearZFamilyM hσ hB rfl
  have h2 : lC ∈ shearXFamilyM C_X C_Z σ hσ := shearX_mem_shearXFamilyM hσ hC rfl
  rw [hGeq]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2))
    (Subgroup.mem_sup_left h1)

end CliffordCSS

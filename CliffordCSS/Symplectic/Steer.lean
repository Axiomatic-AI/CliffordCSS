import CliffordCSS.Symplectic.Levi
import CliffordCSS.Symplectic.Shear

/-!
# X-steering — carrying a label to the first `X`-generator (Beyond transversality)

Pure mathematics : the first reusable step of the **symplectic
Gaussian elimination** behind the generation theorem for `Sp(2n, 𝔽₂)` (*Beyond transversality*,
arXiv:2608.05688, App. D). Everything is `𝔽₂` symplectic linear algebra naming the raw carrier
`Matrix` and the `cliffordSymplectic` carrier accessor.

## What this file delivers

The **X-steering** lemma `exists_cliffordSymplectic_vecMul_eq_single_inl`: for every nonzero label
vector `v : Fin n ⊕ Fin n → 𝔽₂` there is a Clifford circuit `U` and a pivot wire `p` with

* `v ᵥ* cliffordSymplectic U = e_{X_p}` (the standard first-`X`-generator label at wire `p`),

I.e. the elementary Clifford gates can carry any nonzero label to a single `X`-generator. This is
the inductive move that clears the first coordinate in the direct `𝔽₂` Gaussian elimination proving
`cliffordSymplectic` surjective (W1's headline, a later chunk); relocating the pivot `p` to a fixed
wire is deferred to the induction's reindexing.

## The route (no signs, pure `𝔽₂` tableau)

Write `v = (x | z)`. If the `X`-part `x` is nonzero, pick a pivot `p` with `x_p = 1`.

* **The `𝔽₂` `GL` step is a self-inverse row replacement.** `updateRow 1 p x` — the identity with
  its `p`-th row overwritten by `x` — is *its own inverse* over `𝔽₂` when `x_p = 1`
  (`updateRow_one_mul_self`, no determinant needed), hence a unit `K ∈ GL(n, 𝔽₂)`, and
  `x ᵥ* K = e_p` (`vecMul_updateRow_one_eq_single`). The Levi engine (chunk 2a) realises
  `leviGate K` by a CNOT circuit, sending the `X`-block to `e_p` (and the `Z`-block to a residual).
* **A symmetric `Z`-shear kills the residual.** `steerShear p z'` is the symmetric matrix whose
  `p`-th row (and column) is `z'` (`steerShear_isSymm`), so `e_p ᵥ* steerShear p z' = z'`
  (`vecMul_single_steerShear`); the shear engine (chunk 2b) realises `shearZ (steerShear p z')` by
  a phase/`CZ` circuit, and over `𝔽₂` the deposit cancels the residual (`z' + z' = 0`), giving
  `e_{X_p}`.

If the `X`-part is zero, `z` is nonzero; a single Hadamard on a wire where `z` is `1` swaps that
`X`/`Z` pair, giving a nonzero `X`-part, and the previous case applies to the transformed label.

Reuse: the two generation engines `exists_cliffordSymplectic_eq_leviGate` (chunk 2a) and
`exists_cliffordSymplectic_eq_shearZ` (chunk 2b), the Hadamard image `cliffordSymplectic_had`
(chunk 1), and the label actions `vecMul_leviGate` / `vecMul_shearZ` / `vecMul_hadamardSymplectic`.
Composition of circuits is `cliffordSymplectic_append` (an anti-homomorphism to the matrix product).
-/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The `𝔽₂` `GL` step: a self-inverse row replacement -/

/-- Over `𝔽₂`, if `x p = 1` then the identity with its `p`-th row overwritten by `x` carries `x` to
the standard basis vector `e_p`: `x ᵥ* (updateRow 1 p x) = e_p`. (The `p`-th coordinate is fixed to
`x_p = 1`; every other coordinate `x_k` is cancelled by the copy of `x_k` on the diagonal.) The key
computation behind `updateRow_one_mul_self`: it makes `updateRow 1 p x` self-inverse. -/
theorem vecMul_updateRow_one_eq_single {p : ι} {x : ι → ZMod 2} (hp : x p = 1) :
    x ᵥ* (Matrix.updateRow (1 : Matrix ι ι (ZMod 2)) p x) = Pi.single p 1 := by
  have hdecomp : Matrix.updateRow (1 : Matrix ι ι (ZMod 2)) p x
      = 1 + Matrix.updateRow 0 p (x - Pi.single p 1) := by
    ext i j
    rw [Matrix.add_apply, Matrix.updateRow_apply, Matrix.updateRow_apply, Pi.sub_apply]
    by_cases hi : i = p
    · rw [if_pos hi, if_pos hi, hi, Matrix.one_apply, Pi.single_apply]
      by_cases hj : j = p
      · subst hj; simp
      · rw [if_neg hj, if_neg (fun h => hj h.symm)]; ring
    · rw [if_neg hi, if_neg hi, Matrix.zero_apply, add_zero]
  rw [hdecomp, Matrix.vecMul_add, Matrix.vecMul_one]
  have hrow : x ᵥ* (Matrix.updateRow (0 : Matrix ι ι (ZMod 2)) p (x - Pi.single p 1))
      = x - Pi.single p 1 := by
    rw [Matrix.vecMul_eq_sum, Finset.sum_eq_single p]
    · rw [Matrix.updateRow_self, hp, one_smul]
    · intro i _ hip
      rw [Matrix.updateRow_ne hip]; exact smul_zero (x i)
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [hrow]
  funext k
  have hz2 : ∀ a b : ZMod 2, a + (a - b) = b := by decide
  simp only [Pi.add_apply, Pi.sub_apply]
  exact hz2 (x k) _

/-- Over `𝔽₂`, if `x p = 1` then `updateRow 1 p x` is an involution: `(updateRow 1 p x)² = I`. Hence
it is a unit of `Matrix ι ι 𝔽₂` (its own inverse), a `GL(ι, 𝔽₂)` element — the linear map carrying
`x` to `e_p` used by the Levi engine. Proof: `updateRow_mul` turns the product into
`(updateRow 1 p x).updateRow p (x ᵥ* updateRow 1 p x)`; `vecMul_updateRow_one_eq_single` rewrites
the new row to `e_p = (1) p`, and `updateRow_idem` + `updateRow_eq_self` collapse it to `I`. -/
theorem updateRow_one_mul_self {p : ι} {x : ι → ZMod 2} (hp : x p = 1) :
    (Matrix.updateRow (1 : Matrix ι ι (ZMod 2)) p x) * Matrix.updateRow 1 p x = 1 := by
  rw [Matrix.updateRow_mul, Matrix.one_mul, vecMul_updateRow_one_eq_single hp,
    Matrix.updateRow_idem]
  ext i j
  by_cases hi : i = p <;>
    simp [Matrix.updateRow_apply, Matrix.one_apply, Pi.single_apply, hi, eq_comm]

/-! ### The symmetric `Z`-shear that deposits a chosen residual on the pivot row -/

/-- The symmetric matrix whose `p`-th row (and, by symmetry, `p`-th column) is `w`, and which
vanishes off that row/column: `steerShear p w = (i, j) ↦ w j` if `i = p`, `w i` if `j = p`, else
`0`. It is the parameter of the `Z`-shear that deposits `w` on the pivot's `Z`-coordinates. -/
def steerShear (p : ι) (w : ι → ZMod 2) : Matrix ι ι (ZMod 2) :=
  Matrix.of fun i j => if i = p then w j else if j = p then w i else 0

omit [Fintype ι] in
/-- `steerShear p w` is symmetric, so `shearZ (steerShear p w)` is a genuine `𝔽₂` `Z`-shear
(`shearZ_mem_iff`) and is realised by a phase/`CZ` circuit through the chunk-2b engine. -/
theorem steerShear_isSymm (p : ι) (w : ι → ZMod 2) : (steerShear p w).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, steerShear, Matrix.of_apply]
  by_cases hi : i = p <;> by_cases hj : j = p <;> simp [hi, hj]

/-- The pivot row of `steerShear p w`, read off by the standard basis label: `e_p ᵥ* steerShear p w
= w`. Combined with `vecMul_shearZ`, the shear `shearZ (steerShear p w)` adds exactly `w` to the
`Z`-part of a label whose `X`-part is `e_p`. -/
theorem vecMul_single_steerShear (p : ι) (w : ι → ZMod 2) :
    (Pi.single p (1 : ZMod 2)) ᵥ* steerShear p w = w := by
  rw [Matrix.single_one_vecMul]
  funext j
  simp [Matrix.row_apply, steerShear]

/-! ### X-steering -/

/-- **X-steering, nonzero-`X`-part case.** If the `X`-part `x` is nonzero, a Levi (CNOT) circuit
carries the `X`-block to `e_p` for a pivot `p` with `x_p = 1`, and a symmetric `Z`-shear (phase/`CZ`
circuit) clears the residual `Z`-block, giving the first `X`-generator `e_{X_p}`. -/
private theorem exists_cliffordSymplectic_vecMul_single_inl_of_fst_ne_zero {n : ℕ}
    (x z : Fin n → ZMod 2) (hx : x ≠ 0) :
    ∃ (U : CliffordCircuit n) (p : Fin n),
      (Sum.elim x z) ᵥ* cliffordSymplectic U = Pi.single (Sum.inl p) 1 := by
  obtain ⟨p, hp⟩ : ∃ p, x p = 1 := by
    obtain ⟨p, hp0⟩ := Function.ne_iff.mp hx
    exact ⟨p, (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) (x p) (by simpa using hp0)⟩
  have hAA : (Matrix.updateRow (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p x)
      * Matrix.updateRow 1 p x = 1 := updateRow_one_mul_self hp
  let K : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ :=
    ⟨Matrix.updateRow 1 p x, Matrix.updateRow 1 p x, hAA, hAA⟩
  have hKval : (K : Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.updateRow 1 p x := rfl
  obtain ⟨U1, hU1⟩ := exists_cliffordSymplectic_eq_leviGate K
  obtain ⟨U2, hU2⟩ := exists_cliffordSymplectic_eq_shearZ
    (steerShear p (z ᵥ* ((↑K⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)))
    (steerShear_isSymm _ _)
  refine ⟨U2 ++ U1, p, ?_⟩
  rw [cliffordSymplectic_append, hU1, hU2, ← Matrix.vecMul_vecMul, vecMul_leviGate, hKval,
    vecMul_updateRow_one_eq_single hp, vecMul_shearZ, vecMul_single_steerShear]
  have hzz : (z ᵥ* ((↑K⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ))
      + z ᵥ* ((↑K⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) = 0 := by
    funext k; simpa using (by decide : ∀ a : ZMod 2, a + a = 0) _
  rw [hzz]
  exact Sum.elim_single_zero p 1

/-- **X-steering.** For every nonzero label vector `v : Fin n ⊕ Fin n → 𝔽₂` there is a Clifford
circuit `U` and a pivot wire `p` with `v ᵥ* cliffordSymplectic U = e_{X_p}`: the elementary Clifford
gates carry any nonzero label to a single first-`X`-generator. The first reusable step of the
symplectic Gaussian elimination proving `cliffordSymplectic` surjective (W1). -/
theorem exists_cliffordSymplectic_vecMul_eq_single_inl {n : ℕ}
    (v : Fin n ⊕ Fin n → ZMod 2) (hv : v ≠ 0) :
    ∃ (U : CliffordCircuit n) (p : Fin n),
      v ᵥ* cliffordSymplectic U = Pi.single (Sum.inl p) 1 := by
  set x : Fin n → ZMod 2 := fun i => v (Sum.inl i) with hxdef
  set z : Fin n → ZMod 2 := fun i => v (Sum.inr i) with hzdef
  have hv' : v = Sum.elim x z := by funext s; cases s <;> rfl
  by_cases hx : x = 0
  · -- `X`-part zero: `z` is nonzero; a Hadamard on a `z`-support wire creates a nonzero `X`-part.
    have hz : z ≠ 0 := by
      intro hz0; apply hv; rw [hv', hx, hz0]; funext s; cases s <;> rfl
    obtain ⟨q, hq0⟩ := Function.ne_iff.mp hz
    have hq : z q = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) (z q) (by simpa using hq0)
    have hne : (Pi.single q 1 : Fin n → ZMod 2) ≠ 0 := by
      intro h; have := congrFun h q; simp at this
    obtain ⟨U', p, hU'⟩ := exists_cliffordSymplectic_vecMul_single_inl_of_fst_ne_zero
      (Pi.single q 1 : Fin n → ZMod 2) (Function.update z q 0) hne
    refine ⟨U' ++ [CliffordGate.had q], p, ?_⟩
    rw [hv', hx, cliffordSymplectic_append, cliffordSymplectic_had, ← Matrix.vecMul_vecMul,
      vecMul_hadamardSymplectic, hq, Pi.zero_apply]
    exact hU'
  · rw [hv']
    exact exists_cliffordSymplectic_vecMul_single_inl_of_fst_ne_zero x z hx

end CliffordCSS

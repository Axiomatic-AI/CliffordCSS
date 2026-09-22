import CliffordCSS.Symplectic.Steer
import CliffordCSS.Symplectic.XShear
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Fixing the first symplectic pair (Beyond transversality)

Pure mathematics : the reduction step of the **symplectic Gaussian
elimination** behind the generation theorem for `Sp(2n, 𝔽₂)` (*Beyond transversality*,
arXiv:2608.05688, App. D). Everything is `𝔽₂` symplectic linear algebra naming the raw carrier
`Matrix` and the `cliffordSymplectic` carrier accessor.

## What this file delivers

`exists_cliffordSymplectic_fixFirstPair`: for every `M ∈ Sp(2(n+1), 𝔽₂)` there is a Clifford
circuit `U` with

* `e_{X_0} ᵥ* (M * cliffordSymplectic U) = e_{X_0}` and
* `e_{Z_0} ᵥ* (M * cliffordSymplectic U) = e_{Z_0}`,

I.e. the elementary Clifford gates carry `M` to a symplectic matrix that **fixes the first
hyperbolic pair** `(X₀, Z₀)`. This is the symplectic (`𝔽₂`-tableau) analogue of the
Pauli-normalizer reduction `IsPauliNormalizer.exists_cliffordCircuit_fixFirstPair`; it is the
inductive step of the generation/surjectivity theorem (W1's headline, a later chunk), where the
residual — necessarily block-diagonal on the complement of wire `0`, since a symplectic map fixing
a hyperbolic pair preserves its symplectic complement — is handled by the induction hypothesis on
the remaining wires.

## The route (no signs, pure `𝔽₂` tableau)

Write `e_{X_0} = Pi.single (Sum.inl 0) 1`, `e_{Z_0} = Pi.single (Sum.inr 0) 1`.

* **X-steering to wire 0** (`exists_cliffordSymplectic_vecMul_eq_single_inl_zero`). The first row
  `v = e_{X_0} ᵥ* M` is nonzero (symplecticity: `⟨v, e_{Z_0} ᵥ* M⟩ = ⟨e_{X_0}, e_{Z_0}⟩ = 1`).
  X-steering (`exists_cliffordSymplectic_vecMul_eq_single_inl`) carries it to `e_{X_p}` for some
  pivot `p`; a **swap Levi gate** `leviGate (permMatrix (swap 0 p))` relocates the pivot to wire
  `0`, giving `e_{X_0} ᵥ* (M * S₁) = e_{X_0}`.

* **Z-steering fixing `e_{X_0}`** (`exists_cliffordSymplectic_vecMul_zsteer`). With the first
  generator fixed, the paired image `b = e_{Z_0} ᵥ* (M S₁)` has `b_{Z_0} = 1`
  (`⟨e_{X_0}, b⟩ = ⟨e_{X_0}, e_{Z_0}⟩ = 1`, and `⟨e_{X_0}, ·⟩` reads the `Z₀`-coordinate,
  `symplecticForm_single_inl`). Two moves that fix `e_{X_0}` carry `b` to `e_{Z_0}`:
  1. a **`Z`-block `GL` step** — the self-inverse `leviGate (Lᵀ)` with `L = updateRow 1 0 b_Z`
     (`updateRow_one_mul_self`) — sends the `Z`-part `b_Z` to `e_0`
     (`vecMul_updateRow_one_eq_single`) while fixing `e_{X_0}` (its `X`-block acts by `Lᵀ`, whose
     `0`-th column is `e_0`); then
  2. a single **`X`-shear** `shearX (steerShear 0 c)` on the resulting `X`-part `c` clears it
     (`vecMul_single_steerShear`, since the `Z`-part is now the single `e_0`), leaving `e_{Z_0}`.
     `X`-shears fix every pure-`X` vector, in particular `e_{X_0}`.

  Doing the `GL` step *before* the `X`-shear makes the shear's parameter a `steerShear` on a
  single vector (as in `exists_cliffordSymplectic_vecMul_eq_single_inl`), avoiding a symmetric
  solve.

Reuse: X-steering (`exists_cliffordSymplectic_vecMul_eq_single_inl`), the Levi and `X`-shear
generation engines (`exists_cliffordSymplectic_eq_leviGate`, `exists_cliffordSymplectic_eq_shearX`),
the self-inverse `𝔽₂` `GL` step and symmetric `steerShear` from `CliffordSymplecticSteer.lean`,
the label actions `vecMul_leviGate` / `vecMul_shearX`, functoriality `cliffordSymplectic_append`,
and the form-side membership criterion `mem_binarySymplecticGroup_iff_symplecticForm_vecMul`.
-/

open Matrix

namespace CliffordCSS

variable {n : ℕ}

/-! ### The symplectic form against a pure `X`-generator reads a `Z`-coordinate -/

/-- The twisted inner product of the pure-`X` generator `e_{X_i}` with any label `y` reads off the
`i`-th `Z`-coordinate of `y`: `⟨e_{X_i}, y⟩ = y_{Z_i}`. Since `e_{X_i} = (e_i | 0)` and
`⟨(x|z), (x'|z')⟩ = x·z' + z·x'`, only the `x·z'` term survives, selecting `y (Sum.inr i)`. -/
theorem symplecticForm_single_inl {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (y : ι ⊕ ι → ZMod 2) :
    symplecticForm (Pi.single (Sum.inl i) 1) y = y (Sum.inr i) := by
  rw [symplecticForm_apply]
  have h1 : ((Pi.single (Sum.inl i) 1 : ι ⊕ ι → ZMod 2)) ∘ Sum.inl = Pi.single i 1 := by
    funext k; by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  have h2 : ((Pi.single (Sum.inl i) 1 : ι ⊕ ι → ZMod 2)) ∘ Sum.inr = 0 := by
    funext k; simp
  rw [h1, h2, single_dotProduct, one_mul, zero_dotProduct, add_zero, Function.comp_apply]

/-! ### Relocating the X-steering pivot to wire `0` -/

/-- **X-steering to wire `0`.** For every nonzero label `v` there is a Clifford circuit `U` with
`v ᵥ* cliffordSymplectic U = e_{X_0}`: X-steering (`exists_cliffordSymplectic_vecMul_eq_single_inl`)
carries `v` to `e_{X_p}` for some pivot `p`, and the swap Levi gate `leviGate (permMatrix (swap 0
p))` relocates the pivot to wire `0`. (When `p = 0` the swap is the identity.) -/
theorem exists_cliffordSymplectic_vecMul_eq_single_inl_zero
    (v : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) (hv : v ≠ 0) :
    ∃ U : CliffordCircuit (n + 1),
      v ᵥ* cliffordSymplectic U = Pi.single (Sum.inl 0) 1 := by
  obtain ⟨U', p, hU'⟩ := exists_cliffordSymplectic_vecMul_eq_single_inl v hv
  have hPP : (Equiv.Perm.permMatrix (ZMod 2) (Equiv.swap (0 : Fin (n + 1)) p))
      * Equiv.Perm.permMatrix (ZMod 2) (Equiv.swap 0 p) = 1 := by
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  set K : (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))ˣ :=
    ⟨Equiv.Perm.permMatrix (ZMod 2) (Equiv.swap 0 p),
      Equiv.Perm.permMatrix (ZMod 2) (Equiv.swap 0 p), hPP, hPP⟩ with hK
  obtain ⟨Usw, hUsw⟩ := exists_cliffordSymplectic_eq_leviGate K
  have hKval : (K : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))
      = Equiv.Perm.permMatrix (ZMod 2) (Equiv.swap 0 p) := by rw [hK]
  have hrow : (Pi.single p 1 : Fin (n + 1) → ZMod 2)
      ᵥ* Equiv.Perm.permMatrix (ZMod 2) (Equiv.swap 0 p) = Pi.single 0 1 := by
    rw [Matrix.vecMul_permMatrix]
    funext j
    rw [Function.comp_apply, Equiv.symm_swap, Pi.single_apply, Pi.single_apply]
    by_cases hj : j = 0
    · subst hj; rw [Equiv.swap_apply_left]; simp
    · rw [if_neg hj, if_neg (fun h => hj ((Equiv.swap 0 p).injective
        (h.trans (Equiv.swap_apply_left 0 p).symm)))]
  refine ⟨Usw ++ U', ?_⟩
  rw [cliffordSymplectic_append, ← Matrix.vecMul_vecMul, hU', hUsw,
    ← Sum.elim_single_zero p (1 : ZMod 2), vecMul_leviGate, hKval, hrow, Matrix.zero_vecMul,
    Sum.elim_single_zero]

/-! ### Z-steering fixing the first `X`-generator -/

/-- **Z-steering fixing `e_{X_0}`.** If a label `b` has `b_{Z_0} = 1`, then a Clifford circuit `U`
built from generators that fix `e_{X_0}` carries `b` to `e_{Z_0}` while keeping `e_{X_0}` fixed:
`e_{X_0} ᵥ* cliffordSymplectic U = e_{X_0}` and `b ᵥ* cliffordSymplectic U = e_{Z_0}`. A `Z`-block
`GL` step (the self-inverse `leviGate (Lᵀ)`, `L = updateRow 1 0 b_Z`) normalises the `Z`-part to
`e_0`, then one `X`-shear `shearX (steerShear 0 c)` clears the residual `X`-part `c`. -/
theorem exists_cliffordSymplectic_vecMul_zsteer
    (b : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) (hb : b (Sum.inr 0) = 1) :
    ∃ U : CliffordCircuit (n + 1),
      (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
          ᵥ* cliffordSymplectic U = Pi.single (Sum.inl 0) 1 ∧
      b ᵥ* cliffordSymplectic U = Pi.single (Sum.inr 0) 1 := by
  set bX : Fin (n + 1) → ZMod 2 := fun i => b (Sum.inl i) with hbXdef
  set bZ : Fin (n + 1) → ZMod 2 := fun i => b (Sum.inr i) with hbZdef
  have hb' : b = Sum.elim bX bZ := by funext s; cases s <;> rfl
  have hbZ0 : bZ 0 = 1 := hb
  set L : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := Matrix.updateRow 1 0 bZ with hLdef
  have hLL : L * L = 1 := updateRow_one_mul_self hbZ0
  have hLTLT : Lᵀ * Lᵀ = 1 := by rw [← Matrix.transpose_mul, hLL, Matrix.transpose_one]
  have hbZL : bZ ᵥ* L = Pi.single 0 1 := vecMul_updateRow_one_eq_single hbZ0
  have hcol0 : (Pi.single (0 : Fin (n + 1)) 1 : Fin (n + 1) → ZMod 2) ᵥ* Lᵀ
      = Pi.single 0 1 := by
    rw [Matrix.vecMul_transpose, Matrix.mulVec_single, MulOpposite.op_one, one_smul]
    funext i
    rw [Matrix.col_apply, hLdef]
    by_cases hi : i = 0
    · subst hi; rw [Matrix.updateRow_self, hbZ0, Pi.single_eq_same]
    · rw [Matrix.updateRow_ne hi, Matrix.one_apply, if_neg hi, Pi.single_apply, if_neg hi]
  set K : (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))ˣ := ⟨Lᵀ, Lᵀ, hLTLT, hLTLT⟩ with hK
  have hKval : (K : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = Lᵀ := by rw [hK]
  have hKK : K * K = 1 := Units.ext (by rw [Units.val_mul, Units.val_one, hKval]; exact hLTLT)
  have hKinv : ((K⁻¹ : (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))ˣ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)) = Lᵀ := by
    rw [inv_eq_of_mul_eq_one_right hKK, hKval]
  obtain ⟨Ulevi, hUlevi⟩ := exists_cliffordSymplectic_eq_leviGate K
  set c : Fin (n + 1) → ZMod 2 := bX ᵥ* Lᵀ with hcdef
  have hleviX : (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* leviGate K
      = Sum.elim (Pi.single 0 1) 0 := by
    rw [← Sum.elim_single_zero (0 : Fin (n + 1)) (1 : ZMod 2), vecMul_leviGate, hKval, hcol0,
      Matrix.zero_vecMul]
  have hleviB : b ᵥ* leviGate K = Sum.elim c (Pi.single 0 1) := by
    rw [hb', vecMul_leviGate, hKval, hKinv, Matrix.transpose_transpose, hbZL, ← hcdef]
  obtain ⟨Ushear, hUshear⟩ := exists_cliffordSymplectic_eq_shearX (steerShear 0 c)
    (steerShear_isSymm 0 c)
  have hshearX :
      (Sum.elim (Pi.single (0 : Fin (n + 1)) 1) 0 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
        ᵥ* shearX (steerShear 0 c) = Sum.elim (Pi.single 0 1) 0 := by
    rw [vecMul_shearX, Matrix.zero_vecMul, add_zero]
  have hcc : c + c = 0 := by funext k; simpa using (by decide : ∀ a : ZMod 2, a + a = 0) (c k)
  have hshearB :
      (Sum.elim c (Pi.single (0 : Fin (n + 1)) 1) : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
        ᵥ* shearX (steerShear 0 c) = Sum.elim (0 : Fin (n + 1) → ZMod 2) (Pi.single 0 1) := by
    rw [vecMul_shearX, vecMul_single_steerShear, hcc]
  refine ⟨Ushear ++ Ulevi, ?_, ?_⟩
  · rw [cliffordSymplectic_append, ← Matrix.vecMul_vecMul, hUlevi, hUshear, hleviX, hshearX,
      Sum.elim_single_zero]
  · rw [cliffordSymplectic_append, ← Matrix.vecMul_vecMul, hUlevi, hUshear, hleviB, hshearB,
      Sum.elim_zero_single]

/-! ### Fixing the first symplectic pair -/

/-- **Fixing the first symplectic pair.** For every `M ∈ Sp(2(n+1), 𝔽₂)` there is a Clifford
circuit `U` with `M * cliffordSymplectic U` fixing both first generators:
`e_{X_0} ᵥ* (M * cliffordSymplectic U) = e_{X_0}` and `e_{Z_0} ᵥ* (M * cliffordSymplectic U) =
e_{Z_0}`. The symplectic (`𝔽₂`-tableau) analogue of
`IsPauliNormalizer.exists_cliffordCircuit_fixFirstPair`, and the reduction step of the
generation/surjectivity theorem for `cliffordSymplectic` (W1).

Proof: X-steer the first row `e_{X_0} ᵥ* M` (nonzero by symplecticity) to `e_{X_0}` at wire `0`
(`exists_cliffordSymplectic_vecMul_eq_single_inl_zero`); then, with `e_{X_0}` fixed, the paired
image `e_{Z_0} ᵥ* (M S₁)` has `Z₀`-coordinate `1` (symplecticity, `symplecticForm_single_inl`), so
Z-steering fixing `e_{X_0}` (`exists_cliffordSymplectic_vecMul_zsteer`) carries it to `e_{Z_0}`. -/
theorem exists_cliffordSymplectic_fixFirstPair
    {M : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)}
    (hM : M ∈ binarySymplecticGroup (Fin (n + 1))) :
    ∃ U : CliffordCircuit (n + 1),
      (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
          ᵥ* (M * cliffordSymplectic U) = Pi.single (Sum.inl 0) 1 ∧
      (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
          ᵥ* (M * cliffordSymplectic U) = Pi.single (Sum.inr 0) 1 := by
  set e0X : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2 := Pi.single (Sum.inl 0) 1 with he0X
  set e0Z : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2 := Pi.single (Sum.inr 0) 1 with he0Z
  have hpair : symplecticForm e0X e0Z = 1 := by
    rw [he0X, he0Z, symplecticForm_single_inl]; simp
  have hv : e0X ᵥ* M ≠ 0 := by
    intro h0
    have hform := (mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mp hM) e0X e0Z
    rw [h0, hpair] at hform
    simp only [symplecticForm, zero_dotProduct] at hform
    exact one_ne_zero hform.symm
  obtain ⟨U₁, hU₁⟩ := exists_cliffordSymplectic_vecMul_eq_single_inl_zero (e0X ᵥ* M) hv
  have hMU₁ : M * cliffordSymplectic U₁ ∈ binarySymplecticGroup (Fin (n + 1)) :=
    mul_mem hM (cliffordSymplectic_mem_binarySymplecticGroup U₁)
  have hfixX : e0X ᵥ* (M * cliffordSymplectic U₁) = e0X := by
    rw [← Matrix.vecMul_vecMul, hU₁, ← he0X]
  set b : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2 :=
    e0Z ᵥ* (M * cliffordSymplectic U₁) with hbdef
  have hbZ0 : b (Sum.inr 0) = 1 := by
    have hform := (mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mp hMU₁) e0X e0Z
    rw [hfixX, ← hbdef] at hform
    rw [← symplecticForm_single_inl 0 b, ← he0X, hform, hpair]
  obtain ⟨U₂, hU₂X, hU₂b⟩ := exists_cliffordSymplectic_vecMul_zsteer b hbZ0
  refine ⟨U₂ ++ U₁, ?_, ?_⟩
  · rw [cliffordSymplectic_append, ← mul_assoc, ← Matrix.vecMul_vecMul, hfixX, he0X, hU₂X]
  · rw [cliffordSymplectic_append, ← mul_assoc, ← Matrix.vecMul_vecMul, ← hbdef, hU₂b,
      he0Z]

end CliffordCSS

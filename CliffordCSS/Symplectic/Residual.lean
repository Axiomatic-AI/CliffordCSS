import CliffordCSS.Symplectic.FirstPair

/-!
# The residual of a symplectic matrix fixing the first pair (Beyond transversality)

Pure mathematics : the **block-diagonal descent** underlying the
generation/surjectivity theorem for `Sp(2n, 𝔽₂)` (*Beyond transversality*, arXiv:2608.05688,
App. D). Everything is `𝔽₂` symplectic linear algebra naming the raw carrier `Matrix`.

## What this file delivers

The reduction step of the symplectic Gaussian elimination
(`CliffordCSS/Symplectic/FirstPair.lean`, `exists_cliffordSymplectic_fixFirstPair`) produces,
from any `M ∈ Sp(2(n+1), 𝔽₂)`, a matrix `N = M * cliffordSymplectic U` that **fixes the first
hyperbolic pair** — `e_{X_0} ᵥ* N = e_{X_0}` and `e_{Z_0} ᵥ* N = e_{Z_0}`. The surjectivity
induction then descends onto the remaining `n` wires. This file supplies the algebra that descent
turns on: a symplectic matrix fixing the first pair is **block-diagonal** (identity on wire `0`, no
coupling between wire `0` and the rest) and so **restricts to a symplectic matrix on the remaining
`n` wires**. It is pure symplectic linear algebra about `N`; it names no Clifford circuit.

* `symplecticForm_single_inr` — the twisted inner product against the pure-`Z` generator `e_{Z_i}`
  reads off the `i`-th `X`-coordinate, `⟨e_{Z_i}, y⟩ = y_{X_i}` (companion of the existing
  `symplecticForm_single_inl`).
* `vecMul_col_inr_of_fixFirstPair` / `vecMul_col_inl_of_fixFirstPair` — **the wire-`0` columns are
  clean**: for `N ∈ Sp(2(n+1), 𝔽₂)` fixing the first pair, column `Z_0` (resp. `X_0`) of `N` is the
  standard basis vector `e_{Z_0}` (resp. `e_{X_0}`), i.e. `N r (Z_0) = e_{Z_0} r`. Rows `X_0, Z_0`
  are standard by the fixing hypothesis; symplecticity forces the paired columns to be standard too.
  Proof: `N r c = ⟨e, e_r ᵥ* N⟩` for the right generator `e` (`symplecticForm_single_inl/inr`),
  `= ⟨e ᵥ* N, e_r ᵥ* N⟩` (the fixed row `e ᵥ* N = e`), `= ⟨e, e_r⟩` (form preservation), `= e_r c`.
* `embedFirstPair` — embed an `n`-wire label onto wires `1.n` (`Fin.succ`), zero on wire `0`, with
  `embedFirstPair_symplecticForm` (it is a symplectic isometry onto the wire-`0` complement) and
  `embedFirstPair_vecMul` (block-diagonality: `embedFirstPair u ᵥ* N = embedFirstPair (u ᵥ*
  residualFirstPair N)`, using column-cleanness for the wire-`0` output coordinates and the
  `Fin.succ`-shift for the rest).
* `residualFirstPair` — the sub-register block `N (Sum.map Fin.succ Fin.succ p) (Sum.map Fin.succ
  Fin.succ q)` of `N` on wires `1.n`.
* `residualFirstPair_mem_binarySymplecticGroup` — **the headline**: the residual lies in
  `Sp(2n, 𝔽₂)`. Its row action is the wire-`1.n` block of `N`'s (block-diagonality,
  `embedFirstPair_vecMul`), `N` preserves the form, and the embedding is an isometry
  (`embedFirstPair_symplecticForm`), so the residual preserves the form of the `n`-wire register
  (`mem_binarySymplecticGroup_iff_symplecticForm_vecMul`).

This is the block-diagonal restriction the descent of the surjectivity theorem (W1's terminal chunk)
feeds to the induction hypothesis on the `n` remaining wires, alongside the reindex bridge
`CliffordCSS/Symplectic/Reindex.lean`.
-/

open Matrix

namespace CliffordCSS

variable {n : ℕ}

/-! ### The symplectic form against a pure `Z`-generator reads an `X`-coordinate -/

/-- The twisted inner product of the pure-`Z` generator `e_{Z_i}` with any label `y` reads off the
`i`-th `X`-coordinate of `y`: `⟨e_{Z_i}, y⟩ = y_{X_i}`. Since `e_{Z_i} = (0 | e_i)` and
`⟨(x|z), (x'|z')⟩ = x·z' + z·x'`, only the `z·x'` term survives, selecting `y (Sum.inl i)`. The
`Z`-side companion of `symplecticForm_single_inl`. -/
theorem symplecticForm_single_inr {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (y : ι ⊕ ι → ZMod 2) :
    symplecticForm (Pi.single (Sum.inr i) 1) y = y (Sum.inl i) := by
  rw [symplecticForm_apply]
  have h1 : ((Pi.single (Sum.inr i) 1 : ι ⊕ ι → ZMod 2)) ∘ Sum.inl = 0 := by
    funext k; simp
  have h2 : ((Pi.single (Sum.inr i) 1 : ι ⊕ ι → ZMod 2)) ∘ Sum.inr = Pi.single i 1 := by
    funext k; by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  rw [h1, h2, zero_dotProduct, zero_add, single_dotProduct, one_mul, Function.comp_apply]

/-! ### The wire-`0` columns of a symplectic matrix fixing the first pair are clean -/

variable {N : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)}

/-- **Column `Z_0` is clean.** If `N ∈ Sp(2(n+1), 𝔽₂)` fixes the first `X`-generator
(`e_{X_0} ᵥ* N = e_{X_0}`), then column `Z_0` of `N` is the standard basis vector `e_{Z_0}`:
`N r (Sum.inr 0) = Pi.single (Sum.inr 0) 1 r` for every row `r`. The row `X_0` is `e_{X_0}` by
hypothesis; symplecticity (`⟨e_{X_0}, ·⟩` reads the `Z_0`-coordinate, `symplecticForm_single_inl`)
propagates it to the paired column. -/
theorem vecMul_col_inr_of_fixFirstPair (hN : N ∈ binarySymplecticGroup (Fin (n + 1)))
    (hX : (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inl 0) 1) (r : Fin (n + 1) ⊕ Fin (n + 1)) :
    N r (Sum.inr 0) = (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) r := by
  have hrow : (Pi.single r 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N = N r :=
    Matrix.single_one_vecMul r N
  have hpres := (mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mp hN)
    (Pi.single (Sum.inl 0) 1) (Pi.single r 1)
  have hval : N r (Sum.inr 0)
      = (Pi.single r 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) (Sum.inr 0) := by
    rw [← symplecticForm_single_inl 0 (N r), ← hrow, ← hX, hpres, symplecticForm_single_inl]
  rw [hval]; simp [Pi.single_apply, eq_comm]

/-- **Column `X_0` is clean.** If `N ∈ Sp(2(n+1), 𝔽₂)` fixes the first `Z`-generator
(`e_{Z_0} ᵥ* N = e_{Z_0}`), then column `X_0` of `N` is the standard basis vector `e_{X_0}`:
`N r (Sum.inl 0) = Pi.single (Sum.inl 0) 1 r`. The `X`-side companion of
`vecMul_col_inr_of_fixFirstPair` (`⟨e_{Z_0}, ·⟩` reads the `X_0`-coordinate,
`symplecticForm_single_inr`). -/
theorem vecMul_col_inl_of_fixFirstPair (hN : N ∈ binarySymplecticGroup (Fin (n + 1)))
    (hZ : (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inr 0) 1) (r : Fin (n + 1) ⊕ Fin (n + 1)) :
    N r (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) r := by
  have hrow : (Pi.single r 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N = N r :=
    Matrix.single_one_vecMul r N
  have hpres := (mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mp hN)
    (Pi.single (Sum.inr 0) 1) (Pi.single r 1)
  have hval : N r (Sum.inl 0)
      = (Pi.single r 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) (Sum.inl 0) := by
    rw [← symplecticForm_single_inr 0 (N r), ← hrow, ← hZ, hpres, symplecticForm_single_inr]
  rw [hval]; simp [Pi.single_apply, eq_comm]

/-! ### The sub-register embedding and the residual block -/

/-- **Embed an `n`-wire label onto wires `1.n`.** `embedFirstPair u` places `u` on the wires
`1, …, n` (via `Fin.succ`) and `0` on wire `0`, on both the `X`- and `Z`-parts:
`embedFirstPair u (Sum.inl i) = Fin.cons 0 (u ∘ Sum.inl) i` and likewise on `Sum.inr`. It is the
right inverse of restriction to the sub-register (`embedFirstPair_map`) and a symplectic isometry
(`embedFirstPair_symplecticForm`). -/
def embedFirstPair (u : Fin n ⊕ Fin n → ZMod 2) : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2 :=
  Sum.elim (Fin.cons 0 (fun k => u (Sum.inl k))) (Fin.cons 0 (fun k => u (Sum.inr k)))

/-- The embedding vanishes on wire `0`'s `X`-coordinate: `embedFirstPair u (Sum.inl 0) = 0`. -/
@[simp] theorem embedFirstPair_inl_zero (u : Fin n ⊕ Fin n → ZMod 2) :
    embedFirstPair u (Sum.inl 0) = 0 := by simp [embedFirstPair]

/-- The embedding vanishes on wire `0`'s `Z`-coordinate: `embedFirstPair u (Sum.inr 0) = 0`. -/
@[simp] theorem embedFirstPair_inr_zero (u : Fin n ⊕ Fin n → ZMod 2) :
    embedFirstPair u (Sum.inr 0) = 0 := by simp [embedFirstPair]

/-- On the embedded coordinate `Sum.map Fin.succ Fin.succ p` the embedding returns `u p`. -/
@[simp] theorem embedFirstPair_map (u : Fin n ⊕ Fin n → ZMod 2) (p : Fin n ⊕ Fin n) :
    embedFirstPair u (Sum.map Fin.succ Fin.succ p) = u p := by
  cases p <;> simp [embedFirstPair]

/-- **Sum against an embedded label peels wire `0`.** Weighting any function `g` on the
`(n+1)`-wire coordinates by `embedFirstPair u` and summing collapses to the `n`-wire sum weighted by
`u`, evaluated on the shifted (`Fin.succ`) coordinates: the wire-`0` terms carry `embedFirstPair u =
0`. The arithmetic core of `embedFirstPair_vecMul`. -/
theorem embedFirstPair_mul_sum (u : Fin n ⊕ Fin n → ZMod 2)
    (g : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) :
    ∑ r, embedFirstPair u r * g r = ∑ p, u p * g (Sum.map Fin.succ Fin.succ p) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [embedFirstPair]

/-- **The residual (sub-register) block** of `N` on wires `1.n`: the `2n × 2n` matrix
`residualFirstPair N p q = N (Sum.map Fin.succ Fin.succ p) (Sum.map Fin.succ Fin.succ q)`, i.e. the
entries of `N` between the wire-`1.n` coordinates. When `N` fixes the first pair and is symplectic
it lies in `Sp(2n, 𝔽₂)` (`residualFirstPair_mem_binarySymplecticGroup`). -/
def residualFirstPair
    (N : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  N.submatrix (Sum.map Fin.succ Fin.succ) (Sum.map Fin.succ Fin.succ)

/-! ### The embedding is a symplectic isometry -/

/-- **The embedding preserves the symplectic form.** Since `embedFirstPair` vanishes on wire `0` and
copies the sub-register onto wires `1.n`, the wire-`0` term of the form drops out and the rest
matches: `⟨embedFirstPair a, embedFirstPair b⟩ = ⟨a, b⟩`. -/
theorem embedFirstPair_symplecticForm (a b : Fin n ⊕ Fin n → ZMod 2) :
    symplecticForm (embedFirstPair a) (embedFirstPair b) = symplecticForm a b := by
  have hcons : ∀ f g : Fin n → ZMod 2,
      (Fin.cons (0 : ZMod 2) f) ⬝ᵥ (Fin.cons (0 : ZMod 2) g) = f ⬝ᵥ g := by
    intro f g
    change ∑ i, Fin.cons (0 : ZMod 2) f i * Fin.cons (0 : ZMod 2) g i = ∑ i, f i * g i
    rw [Fin.sum_univ_succ]
    simp [Fin.cons_succ]
  have e1 : embedFirstPair a ∘ Sum.inl = Fin.cons 0 (a ∘ Sum.inl) := rfl
  have e2 : embedFirstPair a ∘ Sum.inr = Fin.cons 0 (a ∘ Sum.inr) := rfl
  have e3 : embedFirstPair b ∘ Sum.inl = Fin.cons 0 (b ∘ Sum.inl) := rfl
  have e4 : embedFirstPair b ∘ Sum.inr = Fin.cons 0 (b ∘ Sum.inr) := rfl
  rw [symplecticForm_apply, symplecticForm_apply, e1, e2, e3, e4, hcons, hcons]

/-! ### Block-diagonality: the row action of the embedding -/

/-- **Block-diagonality.** For `N ∈ Sp(2(n+1), 𝔽₂)` fixing the first pair, acting on an embedded
label commutes with restriction: `embedFirstPair u ᵥ* N = embedFirstPair (u ᵥ* residualFirstPair
N)`. On the wire-`0` output coordinates both sides vanish — the input is supported off wire `0`, the
wire-`0` columns of `N` are clean (`vecMul_col_inl_of_fixFirstPair` /
`vecMul_col_inr_of_fixFirstPair`); on the wire-`1.n` output coordinates the `Fin.succ`-shifted sum
is exactly the residual's row action. -/
theorem embedFirstPair_vecMul (hN : N ∈ binarySymplecticGroup (Fin (n + 1)))
    (hX : (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inl 0) 1)
    (hZ : (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inr 0) 1) (u : Fin n ⊕ Fin n → ZMod 2) :
    embedFirstPair u ᵥ* N = embedFirstPair (u ᵥ* residualFirstPair N) := by
  -- On the wire-`1.n` output coordinates: the shifted sum is the residual's row action.
  have hmap : ∀ p : Fin n ⊕ Fin n,
      (embedFirstPair u ᵥ* N) (Sum.map Fin.succ Fin.succ p)
        = (u ᵥ* residualFirstPair N) p := by
    intro p
    have hL : (embedFirstPair u ᵥ* N) (Sum.map Fin.succ Fin.succ p)
        = ∑ r, embedFirstPair u r * N r (Sum.map Fin.succ Fin.succ p) := rfl
    rw [hL, embedFirstPair_mul_sum u (fun r => N r (Sum.map Fin.succ Fin.succ p))]
    rfl
  -- On the wire-`0` output coordinates: the embedded input meets the clean wire-`0` columns.
  have hinl0 : (embedFirstPair u ᵥ* N) (Sum.inl 0) = 0 := by
    have hcol : (fun r => N r (Sum.inl 0))
        = (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) :=
      funext (vecMul_col_inl_of_fixFirstPair hN hZ)
    have hL : (embedFirstPair u ᵥ* N) (Sum.inl 0)
        = embedFirstPair u ⬝ᵥ (fun r => N r (Sum.inl 0)) := rfl
    rw [hL, hcol, dotProduct_single_one, embedFirstPair_inl_zero]
  have hinr0 : (embedFirstPair u ᵥ* N) (Sum.inr 0) = 0 := by
    have hcol : (fun r => N r (Sum.inr 0))
        = (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) :=
      funext (vecMul_col_inr_of_fixFirstPair hN hX)
    have hL : (embedFirstPair u ᵥ* N) (Sum.inr 0)
        = embedFirstPair u ⬝ᵥ (fun r => N r (Sum.inr 0)) := rfl
    rw [hL, hcol, dotProduct_single_one, embedFirstPair_inr_zero]
  funext c
  cases c with
  | inl i =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [embedFirstPair_inl_zero]; exact hinl0
    · have h := hmap (Sum.inl k)
      rw [Sum.map_inl] at h
      rw [h]; simp [embedFirstPair]
  | inr i =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [embedFirstPair_inr_zero]; exact hinr0
    · have h := hmap (Sum.inr k)
      rw [Sum.map_inr] at h
      rw [h]; simp [embedFirstPair]

/-! ### The residual is symplectic -/

/-- **The residual of a symplectic matrix fixing the first pair is symplectic.** For
`N ∈ Sp(2(n+1), 𝔽₂)` fixing the first hyperbolic pair, `residualFirstPair N ∈ Sp(2n, 𝔽₂)`.

The residual's row action is the wire-`1.n` block of `N`'s (`embedFirstPair_vecMul`,
block-diagonality); `N` preserves the symplectic form of the `(n+1)`-wire register; and the
embedding is an isometry onto the wire-`0` complement (`embedFirstPair_symplecticForm`). Chaining
these through the form-side criterion `mem_binarySymplecticGroup_iff_symplecticForm_vecMul` shows
the residual preserves the form of the `n`-wire register. This is the block-diagonal restriction the
surjectivity induction (W1's terminal chunk) hands to its induction hypothesis. -/
theorem residualFirstPair_mem_binarySymplecticGroup
    (hN : N ∈ binarySymplecticGroup (Fin (n + 1)))
    (hX : (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inl 0) 1)
    (hZ : (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inr 0) 1) :
    residualFirstPair N ∈ binarySymplecticGroup (Fin n) := by
  rw [mem_binarySymplecticGroup_iff_symplecticForm_vecMul]
  intro u v
  have hpres := (mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mp hN)
    (embedFirstPair u) (embedFirstPair v)
  rw [embedFirstPair_vecMul hN hX hZ u, embedFirstPair_vecMul hN hX hZ v,
    embedFirstPair_symplecticForm, embedFirstPair_symplecticForm] at hpres
  exact hpres

end CliffordCSS

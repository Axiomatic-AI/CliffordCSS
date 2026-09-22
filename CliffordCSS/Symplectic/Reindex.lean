import CliffordCSS.Symplectic.CliffordAction

/-!
# The symplectic locality of circuit relabeling (Beyond transversality)

Pure mathematics : the **reindex bridge** relating the symplectic
matrix of a *relabeled* Clifford circuit to that of the original. Everything is `𝔽₂` symplectic
linear algebra naming the raw carrier `Matrix` and the `cliffordSymplectic` carrier accessor.

## What this file delivers

The circuit layer already carries a wire-embedding operation `CliffordCircuit.relabel f` along an
embedding `f : Fin m ↪ Fin n`, together with the fact that a relabeled circuit acts on the
*embedded* wires exactly as the original on the pulled-back string
(`CliffordCircuit.act_relabel_embed`) and leaves every wire *outside* the range of `f` untouched
(`CliffordCircuit.act_relabel_of_forall_ne`). This file transports that locality through the
symplectic representation `cliffordSymplectic`, giving the two identities the
generation/surjectivity induction for `Sp(2n, 𝔽₂)` needs when it embeds the `n`-wire induction
hypothesis into a sub-register of the `(n+1)`-wire circuit:

* `vecPauli_comp_embedding` — the label bijection commutes with a wire embedding: reading a
  `2n`-label `w` through the embedding `f` (i.e. `vecPauli w ∘ f`) is the same Pauli string as
  `vecPauli` of the pulled-back label `w ∘ (Sum.map f f)`.
* `vecMul_cliffordSymplectic_relabel_map` — **on the embedded coordinates** `Sum.map f f p` the row
  action of the relabeled circuit's symplectic matrix is the row action of the *original's*
  symplectic matrix on the pulled-back label:
  `(w ᵥ* cliffordSymplectic (C.relabel f)) (Sum.map f f p) = (w ∘ Sum.map f f) ᵥ* cliffordSymplectic
  C` at `p`. Concretely, the `m`-wire sub-register block of `cliffordSymplectic (C.relabel f)` is
  exactly `cliffordSymplectic C`.
* `vecMul_cliffordSymplectic_relabel_of_forall_ne` — **off the range of the embedding** the
  relabeled circuit's symplectic matrix acts as the identity:
  `(w ᵥ* cliffordSymplectic (C.relabel f)) q = w q` whenever `q` is not `Sum.map f f p` for any `p`.
  Concretely, the wires not in `f`'s range are fixed — the relabeled matrix couples them to nothing.

Together these say `cliffordSymplectic (C.relabel f)` is the **block-diagonal embedding** of
`cliffordSymplectic C` along `f`: `cliffordSymplectic C` on the sub-register coordinates, the
identity on the complementary coordinates, no coupling between the two. Specialised to
`f = ⟨Fin.succ, Fin.succ_injective n⟩` this is the "peel wire `0`, recurse on the remaining `n`
wires" step of the symplectic Gaussian elimination (W1's headline, a later chunk): the residual of
`exists_cliffordSymplectic_fixFirstPair`, which fixes the first hyperbolic pair, is such a
block-diagonal embedding of an `Sp(2n, 𝔽₂)` matrix, and the induction hypothesis's circuit on the
`n` remaining wires realises it via `relabel`.

## The route

Everything reduces to the label-action description `v ᵥ* cliffordSymplectic U = cliffordLabelMap U v
= checkVec (U.act (vecPauli v))` (`vecMul_cliffordSymplectic`, `cliffordLabelMap_apply`), the
per-coordinate readout `checkVec_inl`/`checkVec_inr`, and the circuit-level locality lemmas
`CliffordCircuit.act_relabel_embed` / `CliffordCircuit.act_relabel_of_forall_ne`. On an embedded
coordinate the readout is transported by `act_relabel_embed` and `vecPauli_comp_embedding`; off the
range it is fixed by `act_relabel_of_forall_ne` and the round-trip `checkVec_vecPauli`.
-/

open Matrix

namespace CliffordCSS

variable {m n : ℕ}

/-- **The label bijection commutes with a wire embedding.** Reading a `2n`-label `w` through
`f : Fin m ↪ Fin n` — the Pauli string `k ↦ vecPauli w (f k)` on the `m`-wire sub-register — is the
same string as `vecPauli` of the pulled-back label `w ∘ (Sum.map f f)`, since both put on wire `k`
the single-qubit Pauli with `X`-bit `w (Sum.inl (f k))` and `Z`-bit `w (Sum.inr (f k))`. -/
theorem vecPauli_comp_embedding (f : Fin m ↪ Fin n) (w : Fin n ⊕ Fin n → ZMod 2) :
    (fun k => vecPauli w (f k)) = vecPauli (fun q => w (Sum.map f f q)) := rfl

/-- **The symplectic matrix of a relabeled circuit acts on the embedded coordinates as the original
on the pulled-back label.** For `f : Fin m ↪ Fin n`, a circuit `C : CliffordCircuit m` and a label
`w`, at every sub-register coordinate `Sum.map f f p`:
`(w ᵥ* cliffordSymplectic (C.relabel f)) (Sum.map f f p) = ((w ∘ Sum.map f f) ᵥ* cliffordSymplectic
C) p`. Equivalently the `m`-wire sub-register block of `cliffordSymplectic (C.relabel f)` is exactly
`cliffordSymplectic C`. Proof: unfold both row actions to `checkVec ∘ act ∘ vecPauli`, read off the
`inl`/`inr` coordinate with `checkVec_inl`/`checkVec_inr`, transport the embedded-wire action with
`CliffordCircuit.act_relabel_embed`, and identify the pulled-back string with `vecPauli` of the
pulled-back label (`vecPauli_comp_embedding`). -/
theorem vecMul_cliffordSymplectic_relabel_map (f : Fin m ↪ Fin n) (C : CliffordCircuit m)
    (w : Fin n ⊕ Fin n → ZMod 2) (p : Fin m ⊕ Fin m) :
    (w ᵥ* cliffordSymplectic (C.relabel f)) (Sum.map f f p)
      = ((fun q => w (Sum.map f f q)) ᵥ* cliffordSymplectic C) p := by
  rw [vecMul_cliffordSymplectic, cliffordLabelMap_apply, vecMul_cliffordSymplectic,
    cliffordLabelMap_apply]
  cases p <;>
    simp only [Sum.map_inl, Sum.map_inr, checkVec_inl, checkVec_inr,
      CliffordCircuit.act_relabel_embed, vecPauli_comp_embedding]

/-- **The symplectic matrix of a relabeled circuit fixes the coordinates outside the embedding.** If
a coordinate `q` is not `Sum.map f f p` for any `p` (its wire lies outside the range of
`f : Fin m ↪ Fin n`), then `(w ᵥ* cliffordSymplectic (C.relabel f)) q = w q`. Equivalently
`cliffordSymplectic (C.relabel f)` restricted to the complementary coordinates is the identity, with
no coupling to the sub-register. Proof: unfold the row action, read off the coordinate, note the
underlying wire is off `f`'s range so `CliffordCircuit.act_relabel_of_forall_ne` leaves it fixed,
and use the label round-trip `checkVec_vecPauli`. -/
theorem vecMul_cliffordSymplectic_relabel_of_forall_ne (f : Fin m ↪ Fin n) (C : CliffordCircuit m)
    (w : Fin n ⊕ Fin n → ZMod 2) {q : Fin n ⊕ Fin n} (hq : ∀ p, Sum.map f f p ≠ q) :
    (w ᵥ* cliffordSymplectic (C.relabel f)) q = w q := by
  rw [vecMul_cliffordSymplectic, cliffordLabelMap_apply]
  cases q with
  | inl k =>
      have hk : ∀ i, f i ≠ k := fun i h => hq (Sum.inl i) (by rw [Sum.map_inl, h])
      rw [checkVec_inl, CliffordCircuit.act_relabel_of_forall_ne f C _ hk, ← checkVec_inl,
        checkVec_vecPauli]
  | inr k =>
      have hk : ∀ i, f i ≠ k := fun i h => hq (Sum.inr i) (by rw [Sum.map_inr, h])
      rw [checkVec_inr, CliffordCircuit.act_relabel_of_forall_ne f C _ hk, ← checkVec_inr,
        checkVec_vecPauli]

end CliffordCSS

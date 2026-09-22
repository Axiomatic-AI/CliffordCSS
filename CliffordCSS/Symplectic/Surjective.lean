import CliffordCSS.Symplectic.Residual
import CliffordCSS.Symplectic.Reindex

/-!
# `cliffordSymplectic` is surjective onto `Sp(2n, 𝔽₂)` (Beyond transversality)

Pure mathematics : the **generation / surjectivity theorem** for the
binary symplectic group `Sp(2n, 𝔽₂)`, the headline of work item **W1** of the certificate-route plan
for Theorem D.1 (*Beyond transversality*, arXiv:2608.05688, App. D). Everything is `𝔽₂` symplectic
linear algebra naming the raw carrier `Matrix` and the `cliffordSymplectic` carrier accessor.

## What this file delivers

The elementary Clifford gates — the single-wire phase gate (a `Z`-shear), the single-wire Hadamard
(the coordinate swap `X_j ↔ Z_j`), and the two-wire CNOT (a block-diagonal transvection pair) —
**generate** the whole group `Sp(2n, 𝔽₂)`; equivalently, the symplectic representation
`cliffordSymplectic` is **surjective onto** `binarySymplecticGroup (Fin n)`.

* `exists_cliffordSymplectic_pow` — every power `(cliffordSymplectic U) ^ m` is itself a gate
  image (repeat `U`), via functoriality `cliffordSymplectic_append`.
* `exists_cliffordSymplectic_mul_eq_one` — every gate image `cliffordSymplectic U` has a **circuit
  right inverse**: `∃ V, cliffordSymplectic U * cliffordSymplectic V = 1`. As an element of the
  *finite group* `↥(binarySymplecticGroup (Fin n))` it has finite order `k = orderOf`, so
  `(cliffordSymplectic U) ^ k = 1`, and `(cliffordSymplectic U) ^ (k - 1)` — a power, hence a
  circuit image — is the inverse. No `Matrix.inv`, no complex-unitary bridge.
* `single_map_succ_eq_embedFirstPair` — the standard basis vector at an embedded coordinate is the
  `embedFirstPair` of the sub-register basis vector.
* `cliffordSymplectic_relabel_succ_of_fixFirstPair` — **the block-diagonal reconstruction**: for
  `N ∈ Sp(2(n+1), 𝔽₂)` fixing the first pair, if a circuit `V` realises the residual
  (`cliffordSymplectic V = residualFirstPair N`), then its `Fin.succ`-relabel realises `N` itself
  (`cliffordSymplectic (V.relabel succ) = N`). Combines the residual's block-diagonality
  (`embedFirstPair_vecMul`) with the reindex bridge (`vecMul_cliffordSymplectic_relabel_map` /
  `…_of_forall_ne`): `N` and `cliffordSymplectic (V.relabel succ)` agree on the wire-`0` rows (both
  fix the first pair) and on the embedded rows (both are the block-diagonal embedding of the
  residual).
* `exists_cliffordSymplectic_of_mem_binarySymplecticGroup` — **the generation theorem**: every
  `M ∈ Sp(2n, 𝔽₂)` is `cliffordSymplectic U` for some circuit `U`. Induction on `n`: the base case
  is the empty register (`Sp(0)` is a singleton); the step fixes the first pair
  (`exists_cliffordSymplectic_fixFirstPair`), descends to the residual on the remaining `n` wires
  (`residualFirstPair_mem_binarySymplecticGroup` + induction hypothesis), rebuilds the correcting
  circuit by the reconstruction lemma, and inverts the first-pair correction by the circuit right
  inverse.
* `cliffordSymplectic_surjective` — the same fact packaged as `Function.Surjective` onto the group
  `↥(binarySymplecticGroup (Fin n))`.

This closure result is the route the certificate-route completeness step (W4) takes to discharge
Lemma D.4 without a `2^16`-element sieve: reachability of the terminal blocks follows from
reachability of the generators.
-/

open Matrix

namespace CliffordCSS

variable {n : ℕ}

/-- **The standard basis vector at an embedded coordinate is the embedding of a sub-register basis
vector.** For `p : Fin n ⊕ Fin n`, `Pi.single (Sum.map Fin.succ Fin.succ p) 1 = embedFirstPair
(Pi.single p 1)`: both vanish on wire `0` and put a single `1` at the shifted coordinate `p`. Used
to recognise an embedded row `Pi.single (Sum.inl (Fin.succ k)) 1` as an `embedFirstPair` input, so
the
block-diagonality lemmas apply. -/
theorem single_map_succ_eq_embedFirstPair (p : Fin n ⊕ Fin n) :
    (Pi.single (Sum.map Fin.succ Fin.succ p) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
      = embedFirstPair (Pi.single p 1) := by
  have hinj : Function.Injective (Sum.map (Fin.succ : Fin n → Fin (n + 1)) Fin.succ) :=
    Sum.map_injective.mpr ⟨Fin.succ_injective n, Fin.succ_injective n⟩
  have hne_map_inl0 : ∀ q : Fin n ⊕ Fin n,
      Sum.map Fin.succ Fin.succ q ≠ (Sum.inl 0 : Fin (n + 1) ⊕ Fin (n + 1)) := by
    intro q; cases q <;> simp [Fin.succ_ne_zero]
  have hne_map_inr0 : ∀ q : Fin n ⊕ Fin n,
      Sum.map Fin.succ Fin.succ q ≠ (Sum.inr 0 : Fin (n + 1) ⊕ Fin (n + 1)) := by
    intro q; cases q <;> simp [Fin.succ_ne_zero]
  funext c
  cases c with
  | inl i =>
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [embedFirstPair_inl_zero, Pi.single_apply, if_neg (fun h => hne_map_inl0 p h.symm)]
      · have hc : (Sum.inl (Fin.succ k) : Fin (n + 1) ⊕ Fin (n + 1))
            = Sum.map Fin.succ Fin.succ (Sum.inl k) := rfl
        rw [hc, embedFirstPair_map]
        simp only [Pi.single_apply, hinj.eq_iff]
  | inr i =>
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [embedFirstPair_inr_zero, Pi.single_apply, if_neg (fun h => hne_map_inr0 p h.symm)]
      · have hc : (Sum.inr (Fin.succ k) : Fin (n + 1) ⊕ Fin (n + 1))
            = Sum.map Fin.succ Fin.succ (Sum.inr k) := rfl
        rw [hc, embedFirstPair_map]
        simp only [Pi.single_apply, hinj.eq_iff]

/-- **Every power of a gate image is a gate image.** `(cliffordSymplectic U) ^ m =
cliffordSymplectic V` for `V = U` repeated `m` times; by induction on `m` using
`cliffordSymplectic_nil` and `cliffordSymplectic_append`. -/
theorem exists_cliffordSymplectic_pow (U : CliffordCircuit n) (m : ℕ) :
    ∃ V : CliffordCircuit n, cliffordSymplectic V = cliffordSymplectic U ^ m := by
  induction m with
  | zero => exact ⟨[], by rw [cliffordSymplectic_nil, pow_zero]⟩
  | succ m ih =>
      obtain ⟨V, hV⟩ := ih
      exact ⟨V ++ U, by rw [cliffordSymplectic_append, hV, ← pow_succ']⟩

/-- **Every gate image has a circuit right inverse.** For any circuit `U`,
`∃ V, cliffordSymplectic U * cliffordSymplectic V = 1`. `cliffordSymplectic U` lies in the finite
group `↥(binarySymplecticGroup (Fin n))`, so it has finite order `k = orderOf`; then
`(cliffordSymplectic U) ^ k = 1`, and `V` realising the power `(cliffordSymplectic U) ^ (k - 1)`
(`exists_cliffordSymplectic_pow`) is the right inverse. This is the closure of the range of
`cliffordSymplectic` under inverses — obtained from the finite-group order, no matrix inverse. -/
theorem exists_cliffordSymplectic_mul_eq_one (U : CliffordCircuit n) :
    ∃ V : CliffordCircuit n, cliffordSymplectic U * cliffordSymplectic V = 1 := by
  have hmem : cliffordSymplectic U ∈ binarySymplecticGroup (Fin n) :=
    cliffordSymplectic_mem_binarySymplecticGroup U
  let a : ↥(binarySymplecticGroup (Fin n)) := ⟨cliffordSymplectic U, hmem⟩
  have hcoe : (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) = cliffordSymplectic U := rfl
  have hpos : 0 < orderOf a := orderOf_pos a
  have hone : cliffordSymplectic U ^ orderOf a = 1 := by
    have h : (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) ^ orderOf a = 1 := by
      rw [← SubmonoidClass.coe_pow, pow_orderOf_eq_one a, OneMemClass.coe_one]
    rwa [hcoe] at h
  obtain ⟨V, hV⟩ := exists_cliffordSymplectic_pow U (orderOf a - 1)
  exact ⟨V, by rw [hV, ← pow_succ', Nat.sub_add_cancel hpos]; exact hone⟩

/-- **The block-diagonal reconstruction step.** Let `N ∈ Sp(2(n+1), 𝔽₂)` fix the first hyperbolic
pair, and let a circuit `V` on the remaining `n` wires realise the residual
(`cliffordSymplectic V = residualFirstPair N`). Then relabeling `V` onto wires `1, …, n` realises
`N` itself: `cliffordSymplectic (V.relabel (Fin.succEmb n)) = N`.

Both matrices agree row by row: on the wire-`0` rows `X_0, Z_0` because both fix the first pair
(`hX`/`hZ` for `N`; the reindex bridge fixes wire `0` for the relabel), and on the embedded rows
because both are the block-diagonal embedding of `residualFirstPair N` — for `N` by
`embedFirstPair_vecMul`, for the relabel by `vecMul_cliffordSymplectic_relabel_map` together with
`cliffordSymplectic V = residualFirstPair N`. This is the descent the surjectivity induction uses to
rebuild the correcting circuit from the induction hypothesis on the residual. -/
theorem cliffordSymplectic_relabel_succ_of_fixFirstPair
    {N : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)}
    (hN : N ∈ binarySymplecticGroup (Fin (n + 1)))
    (hX : (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inl 0) 1)
    (hZ : (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) ᵥ* N
        = Pi.single (Sum.inr 0) 1)
    {V : CliffordCircuit n} (hV : cliffordSymplectic V = residualFirstPair N) :
    cliffordSymplectic (V.relabel (Fin.succEmb n)) = N := by
  have hneX : ∀ q : Fin n ⊕ Fin n,
      Sum.map (⇑(Fin.succEmb n)) (⇑(Fin.succEmb n)) q ≠ Sum.inl 0 := by
    intro q; cases q <;> simp [Fin.succ_ne_zero]
  have hneZ : ∀ q : Fin n ⊕ Fin n,
      Sum.map (⇑(Fin.succEmb n)) (⇑(Fin.succEmb n)) q ≠ Sum.inr 0 := by
    intro q; cases q <;> simp [Fin.succ_ne_zero]
  -- The relabel acts block-diagonally on embedded inputs, matching the residual.
  have hW_embed : ∀ u : Fin n ⊕ Fin n → ZMod 2,
      embedFirstPair u ᵥ* cliffordSymplectic (V.relabel (Fin.succEmb n))
        = embedFirstPair (u ᵥ* residualFirstPair N) := by
    intro u
    funext c
    cases c with
    | inl i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · rw [vecMul_cliffordSymplectic_relabel_of_forall_ne (Fin.succEmb n) V _ hneX,
            embedFirstPair_inl_zero, embedFirstPair_inl_zero]
        · have key := vecMul_cliffordSymplectic_relabel_map (Fin.succEmb n) V
            (embedFirstPair u) (Sum.inl k)
          simp only [Sum.map_inl, Fin.coe_succEmb, embedFirstPair_map] at key
          rw [key, hV]
          exact (embedFirstPair_map (u ᵥ* residualFirstPair N) (Sum.inl k)).symm
    | inr i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · rw [vecMul_cliffordSymplectic_relabel_of_forall_ne (Fin.succEmb n) V _ hneZ,
            embedFirstPair_inr_zero, embedFirstPair_inr_zero]
        · have key := vecMul_cliffordSymplectic_relabel_map (Fin.succEmb n) V
            (embedFirstPair u) (Sum.inr k)
          simp only [Sum.map_inr, Fin.coe_succEmb, embedFirstPair_map] at key
          rw [key, hV]
          exact (embedFirstPair_map (u ᵥ* residualFirstPair N) (Sum.inr k)).symm
  -- The relabel fixes the first pair: its wire-`0` rows are the standard generators.
  have hzeroInl : (fun q => (Pi.single (Sum.inl 0) 1 :
      Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) (Sum.map Fin.succ Fin.succ q))
      = (0 : Fin n ⊕ Fin n → ZMod 2) := by
    funext q; cases q <;> simp [Fin.succ_ne_zero]
  have hzeroInr : (fun q => (Pi.single (Sum.inr 0) 1 :
      Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) (Sum.map Fin.succ Fin.succ q))
      = (0 : Fin n ⊕ Fin n → ZMod 2) := by
    funext q; cases q <;> simp [Fin.succ_ne_zero]
  have hWfixX : (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
      ᵥ* cliffordSymplectic (V.relabel (Fin.succEmb n)) = Pi.single (Sum.inl 0) 1 := by
    funext c
    cases c with
    | inl i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · exact vecMul_cliffordSymplectic_relabel_of_forall_ne (Fin.succEmb n) V _ hneX
        · have key := vecMul_cliffordSymplectic_relabel_map (Fin.succEmb n) V
            (Pi.single (Sum.inl 0) 1) (Sum.inl k)
          simp only [Sum.map_inl, Fin.coe_succEmb] at key
          rw [key, hzeroInl, zero_vecMul, Pi.zero_apply, Pi.single_apply, if_neg]
          exact fun h => Fin.succ_ne_zero k (Sum.inl_injective h)
    | inr i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · exact vecMul_cliffordSymplectic_relabel_of_forall_ne (Fin.succEmb n) V _ hneZ
        · have key := vecMul_cliffordSymplectic_relabel_map (Fin.succEmb n) V
            (Pi.single (Sum.inl 0) 1) (Sum.inr k)
          simp only [Sum.map_inr, Fin.coe_succEmb] at key
          rw [key, hzeroInl, zero_vecMul, Pi.zero_apply, Pi.single_apply, if_neg]
          exact fun h => Sum.inl_ne_inr h.symm
  have hWfixZ : (Pi.single (Sum.inr 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
      ᵥ* cliffordSymplectic (V.relabel (Fin.succEmb n)) = Pi.single (Sum.inr 0) 1 := by
    funext c
    cases c with
    | inl i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · exact vecMul_cliffordSymplectic_relabel_of_forall_ne (Fin.succEmb n) V _ hneX
        · have key := vecMul_cliffordSymplectic_relabel_map (Fin.succEmb n) V
            (Pi.single (Sum.inr 0) 1) (Sum.inl k)
          simp only [Sum.map_inl, Fin.coe_succEmb] at key
          rw [key, hzeroInr, zero_vecMul, Pi.zero_apply, Pi.single_apply, if_neg]
          exact fun h => Sum.inr_ne_inl h.symm
    | inr i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · exact vecMul_cliffordSymplectic_relabel_of_forall_ne (Fin.succEmb n) V _ hneZ
        · have key := vecMul_cliffordSymplectic_relabel_map (Fin.succEmb n) V
            (Pi.single (Sum.inr 0) 1) (Sum.inr k)
          simp only [Sum.map_inr, Fin.coe_succEmb] at key
          rw [key, hzeroInr, zero_vecMul, Pi.zero_apply, Pi.single_apply, if_neg]
          exact fun h => Fin.succ_ne_zero k (Sum.inr_injective h)
  -- Compare the two matrices row by row.
  have hrow : ∀ r, (cliffordSymplectic (V.relabel (Fin.succEmb n))) r = N r := by
    intro r
    have h1 : (cliffordSymplectic (V.relabel (Fin.succEmb n))) r
        = Pi.single r 1 ᵥ* cliffordSymplectic (V.relabel (Fin.succEmb n)) :=
      (Matrix.single_one_vecMul r _).symm
    have h2 : N r = Pi.single r 1 ᵥ* N := (Matrix.single_one_vecMul r N).symm
    rw [h1, h2]
    cases r with
    | inl i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · rw [hWfixX, hX]
        · rw [show (Pi.single (Sum.inl (Fin.succ k)) 1 :
              Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
                = embedFirstPair (Pi.single (Sum.inl k) 1) from by
                have := single_map_succ_eq_embedFirstPair (Sum.inl k : Fin n ⊕ Fin n)
                rwa [Sum.map_inl] at this,
            hW_embed, embedFirstPair_vecMul hN hX hZ]
    | inr i =>
        refine Fin.cases ?_ (fun k => ?_) i
        · rw [hWfixZ, hZ]
        · rw [show (Pi.single (Sum.inr (Fin.succ k)) 1 :
              Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2)
                = embedFirstPair (Pi.single (Sum.inr k) 1) from by
                have := single_map_succ_eq_embedFirstPair (Sum.inr k : Fin n ⊕ Fin n)
                rwa [Sum.map_inr] at this,
            hW_embed, embedFirstPair_vecMul hN hX hZ]
  exact Matrix.ext fun r c => congrFun (hrow r) c

/-- **Generation of `Sp(2n, 𝔽₂)` by the elementary Clifford gates.** Every `M ∈ Sp(2n, 𝔽₂)` is the
symplectic image `cliffordSymplectic U` of some Clifford circuit `U`.

Induction on `n`. For `n = 0` the register is empty and `Sp(0, 𝔽₂)` is a singleton, so `M = 1 =
cliffordSymplectic []`. For `n + 1`: `exists_cliffordSymplectic_fixFirstPair` yields a circuit `U₀`
with `N = M * cliffordSymplectic U₀` fixing the first hyperbolic pair; the residual
`residualFirstPair N` is symplectic on the remaining `n` wires
(`residualFirstPair_mem_binarySymplecticGroup`), so the induction hypothesis realises it by a
circuit `V`; the reconstruction lemma `cliffordSymplectic_relabel_succ_of_fixFirstPair` rebuilds `N`
as
`cliffordSymplectic (V.relabel succ)`; and the first-pair correction `cliffordSymplectic U₀` is
undone by its circuit right inverse (`exists_cliffordSymplectic_mul_eq_one`). Assembling,
`M = cliffordSymplectic (Vinv ++ V.relabel succ)`. -/
theorem exists_cliffordSymplectic_of_mem_binarySymplecticGroup :
    ∀ (n : ℕ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)),
      M ∈ binarySymplecticGroup (Fin n) → ∃ U : CliffordCircuit n, cliffordSymplectic U = M := by
  intro n
  induction n with
  | zero =>
      intro M _
      exact ⟨[], by rw [cliffordSymplectic_nil]; exact Subsingleton.elim _ M⟩
  | succ n ih =>
      intro M hM
      obtain ⟨U₀, hX, hZ⟩ := exists_cliffordSymplectic_fixFirstPair hM
      have hN : M * cliffordSymplectic U₀ ∈ binarySymplecticGroup (Fin (n + 1)) :=
        mul_mem hM (cliffordSymplectic_mem_binarySymplecticGroup U₀)
      obtain ⟨V, hV⟩ := ih (residualFirstPair (M * cliffordSymplectic U₀))
        (residualFirstPair_mem_binarySymplecticGroup hN hX hZ)
      have hW : cliffordSymplectic (V.relabel (Fin.succEmb n)) = M * cliffordSymplectic U₀ :=
        cliffordSymplectic_relabel_succ_of_fixFirstPair hN hX hZ hV
      obtain ⟨Vinv, hVinv⟩ := exists_cliffordSymplectic_mul_eq_one U₀
      exact ⟨Vinv ++ V.relabel (Fin.succEmb n), by
        rw [cliffordSymplectic_append, hW, mul_assoc, hVinv, mul_one]⟩


end CliffordCSS

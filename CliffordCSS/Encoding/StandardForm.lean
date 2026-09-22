import CliffordCSS.Encoding.StandardFormCore
import CliffordCSS.Encoding.PhaseCZNetwork
import CliffordCSS.ZMod2

/-!
# The stabilizer encoding circuit `G (10.124) → standard form (10.125)` (N&C, Problem 10.3)

This file is pure mathematics . It completes the **synthesis** half of
Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"): a Clifford circuit that carries the
*trivial* check matrix `G` of Eq. (10.124) — a listing of the single-qubit generators `Z₁, …, Zₙ`,
i.e. every row `(0 | eᵢ)`, the stabilizer of `|0⟩⊗ⁿ` — to the **standard form** of Eq. (10.125),

```
      r n-k-r k | r n-k-r k
   ┌ I A₁ A₂ | B 0 C₂ ┐ ← r pivot (top) generator rows
   │ 0 0 0 | D I E │ ← n-k-r middle generator rows
   └ 0 0 0 | A₂ᵀ 0 I ┘ ← k encoded-Z rows
```

The circuit is the three composed layers introduced across this sub-project
(`dec-prob10-3-synthesis-layers`):

  `encodingCircuit D ws pairs = phaseCZNetwork ws pairs ++ encodingCnotHad D`,

Read right-to-left (`CliffordCircuit.act_append`): the **CNOT + Hadamard core** `encodingCnotHad D`
(`PauliStringEncodingStandardFormCore.lean`) acts first, then the **phase / controlled-`Z` network**
`phaseCZNetwork ws pairs` (`PauliStringEncodingPhaseCZNetwork.lean`) acts last.

## What the two stages contribute

The core `encodingCnotHad D` already deposits every `X`-block and every *coupled* `Z`-block of
(10.125): the top rows' `X`-part `[I A₁ A₂]` (with `Z`-part still `0`), the middle rows `[D I E]`
with the standard-form coupling `D = A₁ᵀ + E A₂ᵀ`, and the encoded-`Z` rows `[A₂ᵀ 0 I]`. The only
blocks left are the **top rows' residual `Z`-blocks `B`, `C₂`**, which the phase/`CZ` network
deposits. Crucially the phase and `CZ` gates only *add* a `Z` reading `X`-bits they never change
(`z += x`), so:

* on the **middle** and **encoded-`Z`** rows, whose `X`-part is identically `0`, the whole phase/`CZ`
  network is the identity (`phaseCZ_fix`): those rows are left exactly as the core produced them —
  `[0 | D I E]` and `[0 | A₂ᵀ 0 I]`;
* on the **pivot** rows, whose `X`-part is `[I A₁ A₂]`, the network deposits the top `Z`-blocks
  `B` (diagonal via the phase layer `sLayer`, off-diagonal via `CZ` between two pivots) and `C₂` (via
  `CZ` between a pivot and an encoded wire). Restricting the phase/`CZ` data to the pivot and encoded
  wires (`ws`, `pairs` avoid the middle wires) keeps the middle `Z`-block of the top rows `0`
  (`phaseCZZ_middle_eq_zero`) — the `0` of `[B 0 C₂]`.

## What is proved

For any partition data `D : StdFormData n` and phase/`CZ` data `ws`, `pairs`:

* `checkRow_encodingCircuit_middle` / `_data` — the middle / encoded-`Z` rows equal the ones the core
  produced (the phase/`CZ` layer fixes them): `[0 | D I E]`, `[0 | A₂ᵀ 0 I]`.
* `checkRow_encodingCircuit_pivot` — a pivot row `p` becomes `(eₚ + 𝟙_{tgt p} | phaseCZZ ws pairs …)`:
  the `X`-blocks `[I A₁ A₂]` unchanged and the top `Z`-blocks `B`, `C₂` deposited as the explicit
  symmetric phase/`CZ` form `phaseCZZ`.
* `phaseCZZ_middle_eq_zero` — the deposited `Z`-block vanishes on the middle columns when `ws`, `pairs`
  avoid the middle wires: the top rows are `[I A₁ A₂ | B 0 C₂]`, the standard form (10.125).
* `encodingCircuit_conj_pauliString` — the **operator (unitary) reading**: the encoding circuit's
  unitary conjugates each trivial generator `P_{Zᵢ}` to `± P_{row i}`, i.e. maps the `|0⟩⊗ⁿ`
  stabilizer to the code's standard-form stabilizer up to sign (`CliffordCircuit.conj_pauliString`,
  the phase nonzero by `sign_ne_zero`).
* `phaseCZZ_of_symm` / `encodingCircuit_standardForm_achievable` — the **achievability** (pinnacle
  claim): the phase/`CZ` deposit realizes every symmetric `𝔽₂`-bilinear form (`phaseCZZ_of_symm`), so
  for **any** standard-form code (`A₁, A₂, E` via `D`, and `B`, `C₂` with the top-row commutation
  relation) there *exists* phase/`CZ` data whose encoding circuit carries `G` (10.124) to that code's
  (10.125) with **exactly** its blocks. The witness `ws = phaseWires G`, `pairs = czPairs G` is read
  off the symmetric phase matrix `G` built from `B`, `C₂`, `A₂`.

The three blocks `A₁, A₂, E` (hence `D`) are already general in the core (`tgt` arbitrary), and the
**achievability** theorem `encodingCircuit_standardForm_achievable` proves the remaining blocks `B`,
`C₂` are too: for any code in standard form — `B` (pivot × pivot), `C₂` (pivot × data) satisfying the
top-row commutation relation `B + Bᵀ = A₂ C₂ᵀ + C₂ A₂ᵀ` — *some* choice of `ws`, `pairs` (avoiding the
middle wires) makes the encoding circuit carry `G` (10.124) to exactly its (10.125). The witness is
the symmetric phase matrix `G` with `G_{PΔ} = C₂`, `G_{PP} = B + A₂ C₂ᵀ` (symmetric by the relation)
and `G_{ΔΔ} = 0`: `phaseCZZ_of_symm` shows the phase/`CZ` deposit is then the bilinear form
`k ↦ Σₗ G k l xₗ`, and the `A₂ C₂ᵀ` contamination the pivot–data `CZ`s inject into the `B`-block
cancels mod `2`.

Everything names only raw index / matrix data (`CliffordCSS.CliffordCircuit`, `Fin n → Fin 4`,
`ZMod 2`).

## Design notes

* `ws`, `pairs` are taken as explicit arguments alongside `D : StdFormData n` (which is frozen) rather
  than bundled: the two families are the free data (`B`, `C₂`), and keeping them separate lets the
  read-offs and the middle-vanishing lemma quantify over them cleanly.
* The phase/`CZ` deposit is packaged once as `phaseCZZ ws pairs x` — evaluated on the pivot `X`-row it
  is the top `Z`-block. Its closed form is obtained from the fold `sCol ws (foldr czCol …)` of
  `checkRow_act_phaseCZNetwork` via the single closed-form fold lemma `czCol_foldr`, which rewrites the
  whole right fold to one pair `(r.1, …)`: the `X`-part is invariant (so every `CZ` reads the *same*
  `X`-row) and the `Z`-part accumulates the per-pair contributions.
* `phaseCZ_fix` (the network fixes an `X`-free row) is the "no interference" fact for the middle /
  encoded rows; it is `czCol_foldr_fixed` (each `CZ` fixes an `X`-free row, `czCol_fixed`) then
  `sCol_fix` (the phase layer likewise).
-/

namespace CliffordCSS

open Matrix

variable {n : ℕ}

/-! ### Folding the phase / controlled-`Z` column operations -/

/-- **The controlled-`Z` fold in closed form**: the right fold of `czCol` over `pairs` starting from
`r` keeps the `X`-part `r.1` (every `CZ` reads it and never changes it) and adds to each `Z`-bit
`r.2 k` the sum over pairs `(c, t)` of `[k = c] x_t + [k = t] x_c`, every `X`-bit read against the
input `r.1`. Since the whole fold is rewritten to an explicit pair, the `X`-invariance and the
`Z`-accumulation are one lemma. -/
theorem czCol_foldr (pairs : List (Fin n × Fin n)) (r : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    pairs.foldr (fun p r => czCol p.1 p.2 r) r
      = (r.1, fun k => r.2 k + (pairs.map
          (fun p => (if k = p.1 then r.1 p.2 else 0) + (if k = p.2 then r.1 p.1 else 0))).sum) := by
  induction pairs with
  | nil => ext k <;> simp
  | cons p ps ih =>
      rw [List.foldr_cons, ih]
      refine Prod.ext rfl ?_
      funext k
      simp only [czCol, List.map_cons, List.sum_cons]
      ring


/-! ### The deposited top-row `Z`-block -/

/-- **The top-row `Z`-block deposited by the phase / controlled-`Z` network** on a check row with
`X`-part `x` (N&C Problem 10.3): a diagonal phase contribution `[k ∈ ws] x_k` (the diagonal of `B`)
plus the symmetric off-diagonal contribution of each `CZ` pair `(c, t)`, `[k = c] x_t + [k = t] x_c`
(off-diagonal `B` between two pivots, `C₂` between a pivot and an encoded wire). Evaluated on a pivot
row's `X`-part `[I A₁ A₂]` it is the top rows' `Z`-block `[B 0 C₂]`. -/
def phaseCZZ (ws : List (Fin n)) (pairs : List (Fin n × Fin n)) (x : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  fun k => (if k ∈ ws then x k else 0)
    + (pairs.map (fun p => (if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0))).sum


/-! ### The stabilizer encoding circuit and its standard-form action -/


/-! ### Realizing an arbitrary symmetric phase form — achievability of every top `Z`-block

The read-offs above compute the action of `encodingCircuit D ws pairs` for *given* phase/`CZ` data.
This last section proves the **achievability** direction of N&C Problem 10.3: for an arbitrary valid
standard form, *some* member of the circuit family carries `G` (10.124) to it with **exactly** the
prescribed blocks. The pivot deposit `phaseCZZ ws pairs` is `𝔽₂`-linear in the `X`-row, and choosing
`(ws, pairs)` from a symmetric matrix `G` realizes the symmetric bilinear form `k ↦ ∑ₗ G k l · xₗ`
(`phaseCZZ_of_symm`); a code's `(B, C₂)` (with the top-row commutation relation
`B + Bᵀ = A₂C₂ᵀ + C₂A₂ᵀ`) is then hit by `G` with `G_{PΔ} = C₂`, `G_{PP} = B + A₂C₂ᵀ` (symmetric by the
relation) and `G_{ΔΔ} = 0` — the `A₂C₂ᵀ` contamination the pivot–data `CZ`s inject into the `B`-block
cancels mod `2` (`encodingCircuit_standardForm_achievable`). -/

/-- In `ZMod 2`, `if a = 1 then x else 0` is `a * x`. -/
theorem zmod2_ite_eq_one_mul (a x : ZMod 2) : (if a = 1 then x else 0) = a * x := by
  rcases zmod2_eq_zero_or_one a with h | h <;> subst h <;> simp

/-- **The phase wires realizing a phase matrix `G`**: the wires carrying a diagonal `1` of `G`
(one `S` gate each, depositing the diagonal of the top `Z`-block). -/
noncomputable def phaseWires (G : Fin n → Fin n → ZMod 2) : List (Fin n) :=
  (Finset.univ.filter (fun k => G k k = 1)).toList

/-- **The controlled-`Z` pairs realizing a phase matrix `G`**: the strictly-ordered pairs `(c, t)`,
`c < t`, carrying an off-diagonal `1` of `G` (one `CZ` each; every unordered pair listed once). -/
noncomputable def czPairs (G : Fin n → Fin n → ZMod 2) : List (Fin n × Fin n) :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2 = 1)).toList

theorem mem_phaseWires {G : Fin n → Fin n → ZMod 2} {k : Fin n} : k ∈ phaseWires G ↔ G k k = 1 := by
  simp [phaseWires]

theorem phaseWires_nodup (G : Fin n → Fin n → ZMod 2) : (phaseWires G).Nodup :=
  Finset.nodup_toList _

theorem mem_czPairs {G : Fin n → Fin n → ZMod 2} {p : Fin n × Fin n} :
    p ∈ czPairs G ↔ p.1 < p.2 ∧ G p.1 p.2 = 1 := by
  simp [czPairs]


theorem czPairs_ne {G : Fin n → Fin n → ZMod 2} {p : Fin n × Fin n} (hp : p ∈ czPairs G) :
    p.1 ≠ p.2 := ne_of_lt (mem_czPairs.mp hp).1

open Finset in
/-- **The controlled-`Z` pair contribution of `czPairs G` is a symmetric matrix row.** For symmetric
`G`, the per-pair `CZ` deposit at wire `k` — `Σ_{(c,t)∈czPairs G} ([k=c] x_t + [k=t] x_c)` — equals
`Σ_{l≠k} G k l · x l`: each unordered pair `{k, l}` with `G k l = 1` contributes `x l` exactly once. -/
theorem czPairs_sum (G : Fin n → Fin n → ZMod 2) (hsymm : ∀ a b, G a b = G b a)
    (x : Fin n → ZMod 2) (k : Fin n) :
    ((czPairs G).map
        (fun p => (if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0))).sum
      = ∑ l ∈ univ.filter (fun l => l ≠ k), G k l * x l := by
  classical
  rw [czPairs, Finset.sum_map_toList]
  -- RHS: restrict to `G k l = 1` (where the summand is nonzero)
  rw [show (∑ l ∈ univ.filter (fun l => l ≠ k), G k l * x l)
        = ∑ l ∈ univ.filter (fun l => l ≠ k ∧ G k l = 1), x l from by
      conv_rhs => rw [← Finset.filter_filter, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun l _ => (zmod2_ite_eq_one_mul (G k l) (x l)).symm)]
  -- LHS: restrict to pairs touching `k` (the only ones contributing)
  rw [show (∑ p ∈ univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2 = 1),
          ((if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0)))
        = ∑ p ∈ (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2 = 1)).filter
            (fun p => p.1 = k ∨ p.2 = k),
            ((if k = p.1 then x p.2 else 0) + (if k = p.2 then x p.1 else 0)) from by
      symm
      apply Finset.sum_filter_of_ne
      intro p _ hfp
      by_contra hcon
      exact hfp (by rw [if_neg (fun h => hcon (Or.inl h.symm)),
        if_neg (fun h => hcon (Or.inr h.symm)), add_zero])]
  -- bijection: a touching pair ↦ its non-`k` endpoint
  refine Finset.sum_bij'
    (fun p _ => if p.1 = k then p.2 else p.1)
    (fun l _ => if k < l then (k, l) else (l, k)) ?_ ?_ ?_ ?_ ?_
  · -- forward maps into the endpoint set
    rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨⟨hlt, hG⟩, htouch⟩ := hp
    rcases htouch with h | h
    · subst h; rw [if_pos rfl]
      exact ⟨(ne_of_lt hlt).symm, hG⟩
    · subst h
      have hak : a ≠ b := ne_of_lt hlt
      rw [if_neg hak]
      exact ⟨hak, by rw [hsymm]; exact hG⟩
  · -- backward maps into the pair set
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl ⊢
    obtain ⟨hne, hG⟩ := hl
    rcases lt_or_gt_of_ne (Ne.symm hne) with h | h
    · rw [if_pos h]; exact ⟨⟨h, hG⟩, Or.inl rfl⟩
    · rw [if_neg (not_lt.mpr (le_of_lt h))]; exact ⟨⟨h, by rw [hsymm]; exact hG⟩, Or.inr rfl⟩
  · -- left inverse
    rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨⟨hlt, _⟩, htouch⟩ := hp
    rcases htouch with h | h
    · subst h; simp [hlt]
    · subst h; simp [ne_of_lt hlt, not_lt.mpr hlt.le]
  · -- right inverse
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl
    obtain ⟨hne, _⟩ := hl
    rcases lt_or_gt_of_ne (Ne.symm hne) with h | h <;>
      simp [h, not_lt.mpr h.le, ne_of_lt h]
  · -- value equality
    rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨⟨hlt, _⟩, htouch⟩ := hp
    rcases htouch with h | h
    · subst h; simp [ne_of_lt hlt]
    · subst h; simp [ne_of_lt hlt, (ne_of_lt hlt).symm]

open Finset in
/-- **The phase / controlled-`Z` deposit realizes any symmetric matrix as a bilinear form.** For
symmetric `G`, choosing `ws = phaseWires G` and `pairs = czPairs G` makes the top-row deposit
`phaseCZZ` at wire `k` the matrix row `Σₗ G k l · xₗ`. Thus the family of phase/`CZ` deposits is
exactly the symmetric `𝔽₂`-bilinear forms — the surjectivity that yields achievability of every
standard form. The diagonal `[k ∈ ws] xₖ` supplies the `k = l` term `G k k · xₖ`
(`zmod2_ite_eq_one_mul`); the off-diagonal `CZ` sum supplies `Σ_{l≠k} G k l · xₗ` (`czPairs_sum`). -/
theorem phaseCZZ_of_symm (G : Fin n → Fin n → ZMod 2) (hsymm : ∀ a b, G a b = G b a)
    (x : Fin n → ZMod 2) (k : Fin n) :
    phaseCZZ (phaseWires G) (czPairs G) x k = ∑ l, G k l * x l := by
  simp only [phaseCZZ]
  rw [czPairs_sum G hsymm x k,
    show (if k ∈ phaseWires G then x k else 0) = G k k * x k from by
      by_cases h : G k k = 1
      · rw [if_pos (mem_phaseWires.mpr h), h, one_mul]
      · rw [if_neg (fun hm => h (mem_phaseWires.mp hm))]
        rcases zmod2_eq_zero_or_one (G k k) with h0 | h1
        · rw [h0, zero_mul]
        · exact absurd h1 h]
  conv_rhs => rw [← Finset.add_sum_erase univ (fun l => G k l * x l) (Finset.mem_univ k)]
  rw [Finset.filter_ne']


end CliffordCSS

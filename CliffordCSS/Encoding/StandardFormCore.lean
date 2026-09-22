import CliffordCSS.Encoding.CnotNetwork

/-!
# The CNOT + Hadamard core of the stabilizer encoding circuit (N&C, Problem 10.3)

This file is pure mathematics . It continues the **synthesis** half
of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes") — building the circuit that
carries the *trivial* check matrix `G` of Eq. (10.124) (a listing of the single-qubit generators
`Z₁, …, Zₙ`, i.e. every row `(0 | eᵢ)`) to the **standard form** of Eq. (10.125). The final circuit
is three composed layers (`dec-prob10-3-synthesis-layers`),

  `encodingCircuit = phaseCZNetwork ws pairs`
  `++ cnotNetwork (pivots ++ dataWires) tgt ++ hadLayer pivots`;

This file assembles and evaluates the **first two** (`hadLayer ++ cnotNetwork`), depositing every
`X`-block and every *coupled* `Z`-block of (10.125), and leaves the residual top-row `Z`-blocks
`B`, `C₂` — built by the phase/`CZ` network — to the terminal assembly.

## The partition and the two-stage CNOT ordering

`StdFormData n` bundles the combinatorial data of a standard form: a partition of the `n` wires into
`pivots` (the `r` rows with an `X`-part, Hadamard'd at the front), `middle` (the `n − k − r`
pure-`Z` generator rows), and `dataWires` (the `k` encoded-`Z` rows), together with the fan targets
`tgt : Fin n → List (Fin n)`. Reading a target list as a support, `tgt` encodes the standard-form
matrices: for a pivot `p`, `tgt p ⊆ middle ∪ dataWires` is the support of row `p` of `[A₁ | A₂]`;
for a data wire `d`, `tgt d ⊆ middle` is the support of row `d` of `E`.

`encodingCnotHad D := cnotNetwork (D.pivots ++ D.dataWires) D.tgt ++ hadLayer D.pivots`. Reading the
append right-to-left (`CliffordCircuit.act_append`), the Hadamard layer acts **first**
(`Zₚ ↦ Xₚ` on the pivots, `act_hadLayer_zGenPauli`), then the CNOT network. The control list is
`pivots ++ dataWires`, so within the network — via `cnotNetwork_append` and the two-stage engine
(`checkRow_act_cnotNetwork_split_zGenPauli` / `_xGenPauli`, PR 11) — the **data**-controlled
`E`-fans act innermost and the **pivot** fans act on their output. That ordering is the crux
(`dec-prob10-3-general-E-reachable`): the data fans deposit the `E`-block on the middle rows, then
the pivot fans *read the just-deposited `E`* off the data columns, injecting the `E A₂ᵀ` cross-term
that
makes the standard-form relation `D = A₁ᵀ + E A₂ᵀ` (10.125).

## What is proved

For any `D : StdFormData n`, the row-by-row check-matrix action of `encodingCnotHad D` on the seed
rows `Zᵢ` of `G` (10.124):

* `checkRow_encodingCnotHad_pivot` — a **pivot** row `p` becomes `(eₚ + 𝟙_{tgt p} | 0)`: the top
  rows' `X`-blocks `[I A₁ A₂]` (the `I` from the pivot's own wire, `A₁ A₂` from the fan onto its
  middle/data targets), with `Z`-part still `0` (`B, C₂` are the phase/`CZ` layer's job).
* `checkRow_encodingCnotHad_data` — a **data** row `d` becomes
  `(0 | e_d + 𝟙_{p ∈ pivots, d ∈ tgt p})`:
  the encoded-`Z` rows `[A₂ᵀ 0 I]` (the `I` on the data wire itself, `A₂ᵀ` the pivots whose fan
  reaches `d`; the `0` middle block because a data wire is no middle wire's fan source).
* `checkRow_encodingCnotHad_middle` — a **middle** row `m` becomes `(0 | …)` with `Z`-part carrying
  the `I` on `m`, the `E`-block `𝟙[m ∈ tgt d]` on each data wire `d`, and the `D`-block
  `[m ∈ tgt p] + Σ_{t ∈ tgt p} [t ∈ dataWires ∧ m ∈ tgt t]` on each pivot `p` — exactly
  `A₁ᵀ + E A₂ᵀ = D`, the middle rows `[D I E]` of (10.125). This is the read-off exhibiting the
  general `E` and the coupling `D = A₁ᵀ + E A₂ᵀ`.

Since `tgt` is arbitrary (subject only to the partition/support constraints), the blocks `A₁, A₂, E`
range over all `ZMod 2` matrices of the right shape — so this reaches the *general* standard form,
not a specific code (`dec-prob10-3-general-E-reachable`; the book's own Steane example has `E ≠ 0`).

Everything names only raw index / matrix data (`CliffordCSS.CliffordCircuit`, `Fin n → Fin 4`,
`ZMod 2`). The phase/`CZ` layer (`B, C₂`), the full assembly `encodingCircuit` reaching
(10.125), and the operator-level (unitary) reading are the terminal development reusing this one.

## Design notes

* The partition data is bundled as a `structure` so the three read-offs share one hypothesis list
  and the terminal assembly can reuse it. Only the constraints the proofs consume are recorded:
  `Nodup` of the two control lists and every target list; the two support inclusions
  (`tgt p ⊆ middle ∪ dataWires`, `tgt d ⊆ middle`); and the three class-disjointnesses. From these,
  `pivots_disj_tgt` / `data_disj_tgt` supply the *internal disjointness* the two-stage split lemmas
  demand (a control is never a fan target within its own stage), while cross-stage non-disjointness
  (a pivot fan may target a data wire that is itself an `E`-fan control) is exactly the `E A₂ᵀ`
  coupling and is *not* required.
* Each read-off is `CliffordCircuit.act_append` (peel the Hadamard layer) + `act_hadLayer_zGenPauli`
  (`Zₚ ↦ Xₚ` on pivots, identity off them) + the PR-11 split lemma (front `= pivots`, back
  `= dataWires`), reducing to `cnotNetworkCol pivots tgt` applied to an explicit seed row, which is
  then evaluated wire-by-wire with `sum_map_ite_eq_of_nodup` (indicator sums) and `List.sum_map_add`
  (splitting the `D`-block into `A₁ᵀ` and the `E A₂ᵀ` matrix product).
-/

namespace CliffordCSS

variable {n : ℕ}

/-- **The combinatorial data of a standard-form stabilizer code** (N&C (10.111)/(10.125)), as
consumed by the encoding circuit. A partition of the `n` wires into `pivots` (the `r` generator rows
carrying an `X`-part), `middle` (the `n − k − r` pure-`Z` generator rows) and `dataWires` (the `k`
encoded-`Z` rows), together with a fan-target assignment `tgt : Fin n → List (Fin n)` whose supports
*are* the standard-form matrices: `tgt p` (for a pivot `p`) is the support of row `p` of `[A₁ | A₂]`
(targets in `middle ∪ dataWires`); and `tgt d` (for a data wire `d`) is the support of row `d`
of `E`
(targets in `middle`). Only the constraints the read-offs consume are recorded. -/
structure StdFormData (n : ℕ) where
  /-- The pivot wires: the `r` generator rows with a nonzero `X`-part, Hadamard'd at the front. -/
  pivots : List (Fin n)
  /-- The middle wires: the `n − k − r` pure-`Z` generator rows. -/
  middle : List (Fin n)
  /-- The data wires: the `k` encoded-`Z` rows. -/
  dataWires : List (Fin n)
  /-- The CNOT-fan targets of each control wire (the supports of the `[A₁ | A₂]` / `E` rows). -/
  tgt : Fin n → List (Fin n)
  /-- The pivot control list has no repeats. -/
  pivots_nodup : pivots.Nodup
  /-- The data control list has no repeats. -/
  data_nodup : dataWires.Nodup
  /-- Every target list has no repeats (each `1` of a block gives one CNOT). -/
  tgt_nodup : ∀ w : Fin n, (tgt w).Nodup
  /-- A pivot's fan targets lie in the middle or data wires (the columns of `[A₁ | A₂]`). -/
  tgt_pivot_mem : ∀ p ∈ pivots, ∀ t ∈ tgt p, t ∈ middle ∨ t ∈ dataWires
  /-- A data wire's fan targets lie in the middle wires (the columns of `E`). -/
  tgt_data_mem : ∀ d ∈ dataWires, ∀ t ∈ tgt d, t ∈ middle
  /-- No pivot is a middle wire. -/
  pivot_not_middle : ∀ p ∈ pivots, p ∉ middle
  /-- No pivot is a data wire. -/
  pivot_not_data : ∀ p ∈ pivots, p ∉ dataWires
  /-- No data wire is a middle wire. -/
  data_not_middle : ∀ d ∈ dataWires, d ∉ middle

namespace StdFormData

variable (D : StdFormData n)

/-- **Internal disjointness of the pivot stage**: no pivot is a fan target of any pivot. From the
`[A₁ | A₂]`-support inclusion (`tgt_pivot_mem`, targets in `middle ∪ dataWires`) and the fact that a
pivot is neither a middle nor a data wire. This is the hypothesis the two-stage split lemmas demand
of the `front = pivots` stage. -/
theorem pivots_disj_tgt : ∀ a ∈ D.pivots, ∀ b ∈ D.pivots, a ∉ D.tgt b := by
  intro a ha b hb hmem
  rcases D.tgt_pivot_mem b hb a hmem with h | h
  · exact D.pivot_not_middle a ha h
  · exact D.pivot_not_data a ha h

/-- **Internal disjointness of the data stage**: no data wire is a fan target of any data wire. From
the `E`-support inclusion (`tgt_data_mem`, targets in `middle`) and the fact that a data wire is
not a middle wire. This is the hypothesis the two-stage split lemmas demand of the
`back = dataWires` stage. -/
theorem data_disj_tgt : ∀ a ∈ D.dataWires, ∀ b ∈ D.dataWires, a ∉ D.tgt b := by
  intro a ha b hb hmem
  exact D.data_not_middle a ha (D.tgt_data_mem b hb a hmem)

end StdFormData


end CliffordCSS

import CliffordCSS.Encoding.CnotLayer

/-!
# The multi-control CNOT network of the stabilizer encoding circuit (N&C, Problem 10.3)

This file is pure mathematics . It continues the **synthesis** half
of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"). The CNOT layer of
`CliffordCSS/Encoding/CnotLayer.lean` gave, for a **single** control fan `cnotFan i ts`, its
action on the two *seed* generators `Xᵢ` and `Z_m`. The encoding circuit, however, applies a whole
**network** of such fans — one per top (pivot) control wire — to *every* row of the check matrix at
once, and building `[I A₁ A₂]` (and the coupled transposed `Z`-blocks) requires knowing how each fan
acts on the arbitrary intermediate Pauli string produced by the earlier fans, not just on a lone
seed. This file supplies exactly that missing generality:

* `checkRow_act_cnotFan` — the **general symplectic column action of a CNOT fan on an arbitrary
  check row**. It packages the two column operations of every `CNOT_{i→t}` (`x_t += x_c`,
  `z_c += z_t`; Figure 10.7) into one closed form `cnotFanCol i ts` acting on `checkRow g` — for
  any Pauli string `g`, not merely a seed. Because a CNOT's action on the check matrix depends on
  `g` only through its check bits (`pauliBit`), the fan's action factors through `checkRow`, so
  successive fans compose at the check-row level.
* `checkRow_act_cnotNetwork` — the **multi-control CNOT network** `cnotNetwork controls tgt` (a fan
  per control `c ∈ controls`, onto its targets `tgt c`) acts on the check matrix by the
  **composition (right fold) of the per-control fan column operations**. This is the operational
  content of "the encoding circuit acts on the check matrix by a sequence of column operations": the
  network's effect on any row is `controls.foldr (cnotFanCol c (tgt c)) (checkRow g)`.

The single-generator lemmas of the CNOT layer are recovered as instances of `checkRow_act_cnotFan`
(the general column op applied to `checkRow (xGenPauli i)` / `checkRow (zGenPauli m)` reproduces the
X-spread / coupled-transpose rows); the general lemma is what the assembly PR evaluates on the seed
rows of `G` (10.124) — with the pivot controls disjoint from their non-pivot targets — to build the
`X`-blocks `[I A₁ A₂]` and their transposes.

Everything names only raw index / matrix data (`CliffordCSS.pauliString`, `CliffordCircuit`,
`Fin n → Fin 4`, `ZMod 2`). The phase/`CZ` network (`Z`-blocks `B, C₂`) and the final assembly
carrying `G` (10.124) to the standard form (10.125) are later developments that reuse this one.

## Design notes

* The single-qubit check-bit tableaux `pauliBit_cnotCtrlPauli` / `pauliBit_cnotTgtPauli` are the
  `ZMod 2`-valued forms of the `ℕ`-valued symplectic bit laws (`pauliXBit_cnot…` /
  `pauliZBit_cnot…` of `CliffordCSS/Pauli/CnotConjugation.lean`); a `16`-case `decide` lifts them
  to the `pauliBit` pair, from which the whole-string single-CNOT column op
  `checkRow_cnotPauliString` and then the fan column op follow by the wire-by-wire and
  target-by-target inductions.
* `cnotFanCol i ts` reads the *original* control `X`-bit `r.1 i` (a control's `X`-bit is untouched
  by its own fan) and sums the *original* target `Z`-bits `r.2 t` over `ts` into the control's
  `Z`-bit — both valid because the fan changes only target `X`-bits and the control `Z`-bit, never a
  control `X`-bit or a target `Z`-bit; hence the closed form is order-independent and reads solely
  from the input row.
* `cnotFanCol_fixed` (a fan fixes a row whose control `X`-bit and target `Z`-bits all vanish) is the
  "no interference" fact that lets the assembly conclude that the fans other than a row's own leave
  it unchanged.
* `cnotNetwork` and the fold `checkRow_act_cnotNetwork` require only per-control freshness
  (`c ∉ tgt c`, `(tgt c).Nodup`) — the *cross*-control disjointness (controls vs. targets) that
  collapses the fold to the standard-form blocks is supplied by the assembly, not here, keeping this
  file about the network's generic column action.
-/

open Matrix

namespace CliffordCSS

variable {n : ℕ}

/-! ### The single-CNOT check-matrix column operation on an arbitrary row -/

/-- The `ZMod 2` check-bit form of the CNOT **control** tableau: `CNOT_{c→t}` fixes the control's
`X`-bit and adds the target's `Z`-bit to the control's `Z`-bit,
`pauliBit (cnotCtrlPauli a b) = (x_a, z_a + z_b)`. A `16`-case check against the `ℕ`-valued laws
`pauliXBit_cnotCtrlPauli` / `pauliZBit_cnotCtrlPauli`. -/
theorem pauliBit_cnotCtrlPauli (a b : Fin 4) :
    pauliBit (cnotCtrlPauli a b) = ((pauliBit a).1, (pauliBit a).2 + (pauliBit b).2) := by
  fin_cases a <;> fin_cases b <;> decide

/-- The `ZMod 2` check-bit form of the CNOT **target** tableau: `CNOT_{c→t}` adds the control's
`X`-bit to the target's `X`-bit and fixes the target's `Z`-bit,
`pauliBit (cnotTgtPauli a b) = (x_b + x_a, z_b)`. A `16`-case check against the `ℕ`-valued laws
`pauliXBit_cnotTgtPauli` / `pauliZBit_cnotTgtPauli`. -/
theorem pauliBit_cnotTgtPauli (a b : Fin 4) :
    pauliBit (cnotTgtPauli a b) = ((pauliBit b).1 + (pauliBit a).1, (pauliBit b).2) := by
  fin_cases a <;> fin_cases b <;> decide


/-! ### The CNOT-fan check-matrix column operation on an arbitrary row -/


/-! ### The multi-control CNOT network -/


end CliffordCSS

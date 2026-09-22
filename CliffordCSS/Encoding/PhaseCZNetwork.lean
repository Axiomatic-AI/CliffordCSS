import CliffordCSS.Encoding.PhaseCZLayer

/-!
# The phase / controlled-`Z` network of the encoding circuit (N&C, Problem 10.3)

This file is pure mathematics . It continues the **synthesis** half
of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"). The phase/`CZ` *gate primitives*
of `CliffordCSS/Encoding/PhaseCZLayer.lean` gave, for a **single** phase gate (via `sLayer`)
and a **single** controlled-`Z` gate `czGate`, their action on the pure-`X` seed generator `Xᵢ`. The
encoding circuit, however, applies a whole **network** of these `Z`-depositing gates — a phase gate
on each pivot wire needing a diagonal `B`-entry, and a controlled-`Z` on each pair of wires carrying
an off-diagonal `B`- or a `C₂`-entry — to *every* row of the check matrix at once. Building the
top-row `Z`-blocks `B` (symmetric) and `C₂` therefore requires knowing how each gate acts on the
*arbitrary* intermediate Pauli string produced by the earlier (Hadamard and CNOT) layers, not just
a lone seed. This file supplies exactly that generality, mirroring the CNOT network of
`CliffordCSS/Encoding/CnotNetwork.lean`:

* `checkRow_act_sLayer` — the **column action of the phase layer on an arbitrary check row**:
  `S` on wire `k` adds the wire's `X`-bit to its `Z`-bit (`z_k += x_k`), fixing every `X`-bit and
  untouched `Z`-bit. Packaged as `sCol ws` acting on `checkRow g` for any `g`, it generalizes the
  seed lemma `checkRow_act_sLayer_xGenPauli`.
* `checkRow_czPauliString` — the **general column action of a single controlled-`Z` on an arbitrary
  check row**: the symmetric `z_c += x_t`, `z_t += x_c` (`X`-bits fixed), packaged as `czCol c t`.
* `checkRow_act_czNetwork` — the **controlled-`Z` network** `czNetwork pairs` (a `CZ` per pair
  `(c, t) ∈ pairs`) acts on the check matrix by the **right fold of the per-pair `czCol`**.
* `checkRow_act_phaseCZNetwork` — the **combined network**
  `phaseCZNetwork ws pairs = sLayer ws ++ czNetwork pairs` acts on the check matrix by the fold of
  the `CZ` column operations followed by the phase-layer operation `sCol ws`. Every one of these
  gates only *adds* a `Z` (`z += x`) reading `X`-bits it never changes, so on the rows produced by
  the earlier layers it deposits exactly `B`, `C₂` and leaves the `X`-blocks fixed.

The seed lemma `checkRow_act_sLayer_xGenPauli` of the phase/`CZ` layer is recovered from
`checkRow_act_sLayer` (`sCol ws` at `checkRow (xGenPauli i)`). The general lemmas are what the
assembly PR evaluates on the rows already carrying `[I A₁ A₂]`, with pivot/encoded pairs chosen from
`B`, `C₂`, to read off the standard-form `Z`-blocks.

Everything names only raw index / matrix data (`CliffordCSS.pauliString`, `CliffordCircuit`,
`Fin n → Fin 4`, `ZMod 2`). The final assembly carrying `G` (10.124) to the standard form
(10.125) is the last development that reuses this one (there, the middle rows carry no `X`-part, so
the phase/`CZ` gates cannot build the `E`-block: the layered circuit reaches (10.125) with `E = 0`,
`D = A₁ᵀ`).

## Design notes

* The `ZMod 2` check-bit tableaux `pauliBit_phasePauli` / `pauliBit_czCtrlPauli` /
  `pauliBit_czTgtPauli` are the pair forms of the `ℕ`-valued symplectic bit laws (`pauliXBit_…` /
  `pauliZBit_…` of earlier files); a `4`- / `16`-case `decide` lifts them to the `pauliBit` pair,
  from which the whole-string column operations follow wire by wire.
* `sCol ws` and `czCol c t` read the *original* `X`-bits of the input row (the phase and `CZ` gates
  never change an `X`-bit), so the closed forms depend on the string only through its check row and
  successive gates compose at the check-row level — exactly as for `cnotFanCol`.
* `czCol_fixed` (a `CZ` fixes a row whose two `X`-bits vanish) is the "no interference" fact the
  assembly uses to conclude that a `CZ` on wires outside a row's `X`-support leaves it unchanged.
* `czStep c t = if c = t then [] else czGate c t _` keeps the network total (self-pairs dropped),
  sidestepping a `c ≠ t` proof threaded through the gate list — the discipline of `cnotStep`; the
  action lemmas re-supply `c ≠ t`. The fold lemma needs per-pair distinctness (`p.1 ≠ p.2`); the
  cross-pair structure that collapses the fold to the standard-form blocks is supplied by the
  assembly, keeping this file about the network's generic column action.
-/

open Matrix

namespace CliffordCSS

variable {n : ℕ}

/-! ### The `ZMod 2` check-bit tableaux of the phase and controlled-`Z` gates -/

/-- The `ZMod 2` check-bit form of the controlled-`Z` **control** tableau: `CZ_{c,t}` fixes the
control's `X`-bit and adds the target's `X`-bit to the control's `Z`-bit,
`pauliBit (czCtrlPauli a b) = (x_a, z_a + x_b)`. A `16`-case check against `pauliXBit_czCtrlPauli` /
`pauliZBit_czCtrlPauli`. -/
theorem pauliBit_czCtrlPauli (a b : Fin 4) :
    pauliBit (czCtrlPauli a b) = ((pauliBit a).1, (pauliBit a).2 + (pauliBit b).1) := by
  fin_cases a <;> fin_cases b <;> decide

/-- The `ZMod 2` check-bit form of the controlled-`Z` **target** tableau: `CZ_{c,t}` fixes the
target's `X`-bit and adds the control's `X`-bit to the target's `Z`-bit,
`pauliBit (czTgtPauli a b) = (x_b, z_b + x_a)` — symmetric with the control. A `16`-case check
against `pauliXBit_czTgtPauli` / `pauliZBit_czTgtPauli`. -/
theorem pauliBit_czTgtPauli (a b : Fin 4) :
    pauliBit (czTgtPauli a b) = ((pauliBit b).1, (pauliBit b).2 + (pauliBit a).1) := by
  fin_cases a <;> fin_cases b <;> decide

/-! ### The phase-layer check-matrix column operation on an arbitrary row -/

/-- The **column operation of the phase layer** `sLayer ws` on a check row `r = (x | z)`:
add each chosen wire's `X`-bit to its own `Z`-bit (`z_k += x_k` for `k ∈ ws`), fixing the `X`-part
and every other `Z`-bit. Applied to the top rows' `X`-identity block it deposits the diagonal of the
`Z`-block `B`. -/
def sCol (ws : List (Fin n)) (r : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (r.1, fun k => r.2 k + (if k ∈ ws then r.1 k else 0))

/-- **The general column action of the phase layer** (N&C Problem 10.3): for distinct wires `ws`,
conjugating an *arbitrary* Pauli string `g` by `sLayer ws` acts on its check row by `sCol ws`
(`z_k += x_k` for `k ∈ ws`; the `X`-part is fixed). Because a phase gate's action
depends on the wire through its check bits, the layer factors through `checkRow` and composes at
the check-row level with the other layers. It subsumes `checkRow_act_sLayer_xGenPauli` (whose
right-hand side is `sCol ws` at `checkRow (xGenPauli i)`). Proved from `act_sLayer` and check-bit
tableau `pauliBit_phasePauli`. -/
theorem checkRow_act_sLayer (ws : List (Fin n)) (g : Fin n → Fin 4) (hnd : ws.Nodup) :
    checkRow (CliffordCircuit.act (sLayer ws) g) = sCol ws (checkRow g) := by
  rw [act_sLayer ws g hnd]
  ext k <;> by_cases hk : k ∈ ws <;> simp [hk, sCol, checkRow, pauliBit_phasePauli]

/-! ### The single controlled-`Z` check-matrix column operation on an arbitrary row -/

/-- The **column operation of a controlled-`Z`** (`CZ_{c,t}`) on a check row `r = (x | z)`: the
symmetric `z_c += x_t`, `z_t += x_c`, fixing the `X`-part and every other `Z`-bit. Reading a
control/target `X`-bit that the gate never changes, it depends on the string only through its check
row. Between two top wires it deposits an off-diagonal entry of `B`, between a top and an encoded
wire an entry of `C₂`. -/
def czCol (c t : Fin n) (r : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (r.1, fun k => r.2 k + (if k = c then r.1 t else 0) + (if k = t then r.1 c else 0))

/-- **The column action of a single controlled-`Z`** (N&C Problem 10.3), `c ≠ t`: conjugating
any Pauli string `g` by `czGate c t h` acts on its check row by `czCol c t` (the symmetric
`z_c += x_t`, `z_t += x_c`; `X`-bits fixed). Proved from `czPauliString_ctrl` / `_tgt` /
`_of_ne` and the check-bit tableaux `pauliBit_czCtrlPauli` / `pauliBit_czTgtPauli`. -/
theorem checkRow_czPauliString {c t : Fin n} (h : c ≠ t) (g : Fin n → Fin 4) :
    checkRow (czPauliString g c t) = czCol c t (checkRow g) := by
  ext k
  · change (pauliBit (czPauliString g c t k)).1 = _
    rcases eq_or_ne k c with rfl | hkc
    · rw [czPauliString_ctrl, pauliBit_czCtrlPauli]; simp [czCol, checkRow]
    · rcases eq_or_ne k t with rfl | hkt
      · rw [czPauliString_tgt g h, pauliBit_czTgtPauli]; simp [czCol, checkRow]
      · rw [czPauliString_of_ne g c t hkc hkt]; simp [czCol, checkRow]
  · change (pauliBit (czPauliString g c t k)).2 = _
    rcases eq_or_ne k c with rfl | hkc
    · rw [czPauliString_ctrl, pauliBit_czCtrlPauli]; simp [czCol, checkRow, if_neg h]
    · rcases eq_or_ne k t with rfl | hkt
      · rw [czPauliString_tgt g h, pauliBit_czTgtPauli]; simp [czCol, checkRow, if_neg (Ne.symm h)]
      · rw [czPauliString_of_ne g c t hkc hkt]; simp [czCol, checkRow, if_neg hkc, if_neg hkt]


/-! ### The controlled-`Z` network -/

/-- A **single controlled-`Z` step** on the pair `(c, t)`: the three-gate circuit `czGate c t`, or
the empty circuit if `c = t` (a self-pair is skipped). This keeps the `CZ` network total. -/
def czStep (c t : Fin n) : CliffordCircuit n :=
  if h : c = t then [] else czGate c t h

/-- The row action of a single `CZ` step with `c ≠ t` is the `CZ` column operation
`czPauliString g c t`. -/
theorem act_czStep_of_ne {c t : Fin n} (h : c ≠ t) (g : Fin n → Fin 4) :
    CliffordCircuit.act (czStep c t) g = czPauliString g c t := by
  rw [czStep, dif_neg h]; exact act_czGate c t h g

/-- The check-row action of a single `CZ` step with `c ≠ t` is the column operation `czCol c t`. -/
theorem checkRow_act_czStep_of_ne {c t : Fin n} (h : c ≠ t) (g : Fin n → Fin 4) :
    checkRow (CliffordCircuit.act (czStep c t) g) = czCol c t (checkRow g) := by
  rw [act_czStep_of_ne h, checkRow_czPauliString h]

/-- The **controlled-`Z` network**: a `CZ` on each pair `(c, t) ∈ pairs`
(`pairs.flatMap (fun p => czStep p.1 p.2)`). With `pairs` the pivot–pivot pairs of the off-diagonal
`B` and the pivot–encoded pairs of `C₂`, this is the `Z`-block-building `CZ` stage of the stabilizer
encoding circuit of N&C Problem 10.3. -/
def czNetwork (pairs : List (Fin n × Fin n)) : CliffordCircuit n :=
  pairs.flatMap (fun p => czStep p.1 p.2)

/-- The network is built one pair at a time:
`czNetwork (p :: ps) = czStep p.1 p.2 ++ czNetwork ps`. -/
theorem czNetwork_cons (p : Fin n × Fin n) (ps : List (Fin n × Fin n)) :
    czNetwork (p :: ps) = czStep p.1 p.2 ++ czNetwork ps := by
  simp only [czNetwork, List.flatMap_cons]

/-- **The controlled-`Z` network acts on the check matrix by a fold of `CZ` column operations.** For
per-pair distinctness (`p.1 ≠ p.2` for every `p ∈ pairs`), conjugating any Pauli string `g` by
`czNetwork pairs` transforms its check row by the right fold of the per-pair `czCol`,
`pairs.foldr (fun p r => czCol p.1 p.2 r) (checkRow g)` — the last pair's `CZ` is innermost (it
transforms `checkRow g` first) and the head is outermost (it acts last), matching `act_append` and
the right-to-left `CliffordCircuit.act` convention. Proved by induction on `pairs` from `act_append`
and the single-step column action `checkRow_act_czStep_of_ne`. -/
theorem checkRow_act_czNetwork :
    ∀ (pairs : List (Fin n × Fin n)), (∀ p ∈ pairs, p.1 ≠ p.2) → ∀ (g : Fin n → Fin 4),
      checkRow (CliffordCircuit.act (czNetwork pairs) g)
        = pairs.foldr (fun p r => czCol p.1 p.2 r) (checkRow g)
  | [], _, g => by simp [czNetwork, CliffordCircuit.act]
  | p :: ps, hyp, g => by
      have hp := hyp p (List.mem_cons_self ..)
      have hps : ∀ p' ∈ ps, p'.1 ≠ p'.2 := fun p' hp' => hyp p' (List.mem_cons_of_mem _ hp')
      rw [czNetwork_cons, act_append, checkRow_act_czStep_of_ne hp,
        checkRow_act_czNetwork ps hps g, List.foldr_cons]

/-! ### The combined phase / controlled-`Z` network -/

/-- The **phase / controlled-`Z` network** of the stabilizer encoding circuit (N&C Problem 10.3):
the phase layer on the wires `ws` (the diagonal of `B`) followed by the controlled-`Z` network on
`pairs` (the off-diagonal `B` and the block `C₂`), `sLayer ws ++ czNetwork pairs`. Applied after the
Hadamard and CNOT layers it deposits the residual top-row `Z`-blocks `B`, `C₂` of the standard form
(10.125). -/
def phaseCZNetwork (ws : List (Fin n)) (pairs : List (Fin n × Fin n)) : CliffordCircuit n :=
  sLayer ws ++ czNetwork pairs

/-- **The phase / controlled-`Z` network acts on the check matrix by a sequence of `Z`-depositing
column operations** (N&C Problem 10.3): for distinct wires `ws` and per-pair-distinct `pairs`,
conjugating any `g` by `phaseCZNetwork ws pairs` transforms its check row by the fold of
the `CZ` operations `czCol` (over `pairs`) followed by the phase-layer op `sCol ws`. Every one
of these gates only adds a `Z` (`z += x`) reading `X`-bits it never changes, so on the rows produced
by the earlier layers (`X`-part `[I A₁ A₂]`) the network deposits exactly the top-row `Z`-blocks
`B`, `C₂` and leaves the `X`-blocks fixed. Proved from `act_append`, the general phase-layer action
`checkRow_act_sLayer`, and the `CZ` network fold `checkRow_act_czNetwork`. This is the third-layer
analogue of `checkRow_act_cnotNetwork`; the assembly evaluates this fold on the seed rows of `G`
(10.124) to read off the standard-form `Z`-blocks. -/
theorem checkRow_act_phaseCZNetwork (ws : List (Fin n)) (pairs : List (Fin n × Fin n))
    (hnd : ws.Nodup) (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2) (g : Fin n → Fin 4) :
    checkRow (CliffordCircuit.act (phaseCZNetwork ws pairs) g)
      = sCol ws (pairs.foldr (fun p r => czCol p.1 p.2 r) (checkRow g)) := by
  rw [phaseCZNetwork, act_append, checkRow_act_sLayer ws _ hnd,
    checkRow_act_czNetwork pairs hpairs g]

end CliffordCSS

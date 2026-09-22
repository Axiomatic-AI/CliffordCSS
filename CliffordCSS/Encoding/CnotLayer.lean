import CliffordCSS.Encoding.Layers

/-!
# The CNOT layer of the stabilizer encoding circuit (Nielsen & Chuang, Problem 10.3)

This file is pure mathematics . It continues the **synthesis**
half of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"): after the Hadamard
layer (`CliffordCSS/Encoding/Layers.lean`) has turned the top `r` rows of the trivial
check matrix `G` of Eq. (10.124) from `Z`-type (`Zᵢ`) into `X`-type (`Xᵢ`), the second layer is
a **network of CNOT gates**, all controlled on those top `X`-rows, that builds the `X`-blocks
`A₁, A₂` of the standard form (10.125) — and, by the coupled column operations of a CNOT,
simultaneously builds the transposed `Z`-blocks `A₁ᵀ` (into the middle generator rows) and `A₂ᵀ`
(into the bottom encoded-`Z` rows). This file delivers the reusable unit of that network: the
**fan of CNOTs from one control**.

## The CNOT fan

`cnotFan i ts` is the circuit applying a CNOT from control wire `i` to each target `t` in a list
`ts` (a self-target `t = i` is dropped, so the fan is total: `cnotStep i t`). With `ts` the
support of row `i` of `[A₁ | A₂]`, `cnotFan i ts` is exactly the CNOT network attached to the
`i`-th top generator. The two column operations of `CNOT_{i→t}` (`x_t += x_c`, `z_c += z_t`;
Figure 10.7) drive the two effects:

* `act_cnotFan_xGenPauli` — the **X-spread** (building row `i` of `A₁, A₂`): applied to the
  `X`-seed `Xᵢ`, the fan produces the Pauli string with an `X` on wire `i` and on every wire in
  `ts` (`xSetPauli (i :: ts)`). Each `CNOT_{i→t}` copies the control's `X` onto the target
  (`x_t += x_c`), so the seed's single `X` fans out to the whole target set. On the check matrix
  this is row `i` becoming `(eᵢ + Σ_{t∈ts} e_t | 0)` — the `I` diagonal entry plus the row's
  `A₁, A₂` entries.
* `act_cnotFan_zGenPauli_of_mem` — the **coupled transpose** (building `A₂ᵀ` / `A₁ᵀ`): applied
  to a pure-`Z` generator `Z_m` with `m ∈ ts`, the fan produces `Z_i Z_m` (`zPairPauli i m`).
  The single gate `CNOT_{i→m}` copies the target's `Z` back onto the control (`z_i += z_m`), so
  a `Z` on a target wire `m` deposits a `Z` on the control wire `i`. Iterated over the top
  controls `i`, this is precisely how a `Z` in the identity block of a bottom (encoded-`Z`) or
  middle row is transposed into column `i` — the blocks `A₂ᵀ` (bottom) and `A₁ᵀ` (middle) of
  (10.125).
* `act_cnotFan_zGenPauli_of_not_mem` — the fan leaves a pure-`Z` generator `Z_m` **unchanged**
  when `m ∉ ts`: a `Z` on a wire the fan neither controls nor targets is untouched, and a `Z` on
  the control itself is preserved (no target carries a `Z` to add). This is what keeps the layer
  from disturbing rows outside its support.

The check-matrix readings (`checkRow_act_cnotFan_xGenPauli`,
`checkRow_act_cnotFan_zGenPauli_of_mem`) and the operator-level readings through the backbone
`CliffordCircuit.conj_pauliString` (`cnotFan_conj_xGenPauli`, `cnotFan_conj_zGenPauli_of_mem`)
record the same facts as check-matrix column operations and as unitary conjugations up to a
nonzero `±1` phase.

Everything names only raw index / matrix data (`CliffordCSS.pauliString`, `CliffordCircuit`,
`Fin n → Fin 4`, `ZMod 2`). The final phase/`CZ` layer (building the residual
`Z`-blocks `B, C₂, E`) and the assembly reaching (10.125) are later developments that reuse this
one.

## Design notes

* `cnotFan i ts = ts.flatMap (cnotStep i)`, so it composes with the other layers as list
  concatenation and its `act`/`sign`/`toMatrix` are the existing `CliffordCircuit` folds —
  nothing new about circuits is introduced, only the specific gate list. The helper
  `cnotStep i t` (`if i = t then [] else [CNOT_{i→t}]`) makes the fan **total** — a self-target
  is simply skipped — which sidesteps carrying a `i ∉ ts` proof through the gate list; the
  action lemmas re-supply `i ∉ ts` and `ts.Nodup` as hypotheses where they are actually needed
  (freshness of each target).
* Both action lemmas need `ts.Nodup`: a target hit twice would have its column operation applied
  twice and, `X`/`Z` bits living in `ZMod 2`, cancel — the clean "spread over exactly the wires
  in `ts`" statement is the one the encoding circuit uses (each `1` of `A` gives one CNOT).
* The single-gate facts `cnotPauliString_fixed` (a fan leaves a control/target pair fixed when
  the control is `I`/`Z` and the target is `I`) and `cnotPauliString_zGenPauli_couple`
  (`CNOT_{i→m} : Z_m ↦ Z_i Z_m`) are read off the tableau of
  `CliffordCSS/Pauli/CnotConjugation.lean`; the layer lemmas are inductions over `ts` on top
  of them.
-/

open Matrix

noncomputable section

namespace CliffordCSS

variable {n : ℕ}

/-! ### Multi-wire generators (rows of the check matrix) -/

/-- The **multi-`X` Pauli string** on a wire list `S`: `X` on every wire in `S`, `I` elsewhere.
The image of the `X`-seed `Xᵢ` under a CNOT fan (`act_cnotFan_xGenPauli`); its check row is
`(1_S | 0)` — a `1` in each `X`-column of `S`. -/
def xSetPauli (S : List (Fin n)) : Fin n → Fin 4 := fun k => if k ∈ S then 1 else 0

/-- The **two-wire `Z` Pauli string** `Z_i Z_m`: `Z` on wires `i` and `m`, `I` elsewhere. The
image of the pure-`Z` generator `Z_m` under a CNOT fan controlled on `i` with `m` a target
(`act_cnotFan_zGenPauli_of_mem`); its check row is `(0 | e_i + e_m)`. -/
def zPairPauli (i m : Fin n) : Fin n → Fin 4 := fun k => if k = i ∨ k = m then 3 else 0

@[simp] theorem xSetPauli_apply (S : List (Fin n)) (k : Fin n) :
    xSetPauli S k = if k ∈ S then 1 else 0 := rfl

@[simp] theorem zPairPauli_apply (i m k : Fin n) :
    zPairPauli i m k = if k = i ∨ k = m then 3 else 0 := rfl

/-! ### The CNOT fan -/

/-- A **single CNOT step** from control `i` to target `t`: the one-gate circuit `[CNOT_{i→t}]`,
or the empty circuit if `t = i` (a self-target is skipped). This keeps the CNOT fan total. -/
def cnotStep (i t : Fin n) : CliffordCircuit n :=
  if h : i = t then [] else [CliffordGate.cnot i t h]

/-- The **CNOT fan** from control wire `i` onto the target wires `ts`: apply a CNOT from `i` to
each `t ∈ ts` (`ts.flatMap (cnotStep i)`). With `ts` the support of row `i` of the `X`-block
`[A₁ | A₂]`, this is the CNOT network attached to the `i`-th top generator in the encoding
circuit of Nielsen & Chuang Problem 10.3. -/
def cnotFan (i : Fin n) (ts : List (Fin n)) : CliffordCircuit n := ts.flatMap (cnotStep i)


/-- The fan is built one target at a time: `cnotFan i (t :: ts) = cnotStep i t ++ cnotFan i ts`. -/
theorem cnotFan_cons (i t : Fin n) (ts : List (Fin n)) :
    cnotFan i (t :: ts) = cnotStep i t ++ cnotFan i ts := by
  simp only [cnotFan, List.flatMap_cons]

/-- **The row action factors over `++`**: conjugating by `U ++ V` applies `V` first, then `U`
(`act (U ++ V) g = act U (act V g)`), since `act` composes gates right-to-left. -/
theorem act_append (U V : CliffordCircuit n) (g : Fin n → Fin 4) :
    CliffordCircuit.act (U ++ V) g = CliffordCircuit.act U (CliffordCircuit.act V g) := by
  induction U with
  | nil => rfl
  | cons γ U ih => simp only [List.cons_append, CliffordCircuit.act, ih]


/-! ### Single-CNOT tableau facts -/


/-! ### The CNOT layer acting on the seed generators -/


/-! ### Check-matrix readings -/


/-! ### Operator-level readings (through the backbone) -/


end CliffordCSS

end

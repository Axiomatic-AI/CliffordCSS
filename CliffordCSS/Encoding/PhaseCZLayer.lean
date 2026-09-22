import CliffordCSS.Encoding.CnotLayer

/-!
# The phase / controlled-`Z` gates of the stabilizer encoding circuit (N&C, Problem 10.3)

This file is pure mathematics . It continues the **synthesis** half
of Nielsen & Chuang **Problem 10.3** ("encoding stabilizer codes"): after the Hadamard layer
(`CliffordCSS/Encoding/Layers.lean`) turns the top `r` rows of the trivial check matrix `G`
of Eq. (10.124) from `Z`-type to `X`-type, and the CNOT layer
(`CliffordCSS/Encoding/CnotLayer.lean`) builds the `X`-blocks `A₁, A₂` (and, coupled, the
transposed `Z`-blocks `A₁ᵀ, A₂ᵀ`), the last synthesis step is a **network of phase (`S`) and
controlled-`Z` gates** that deposits the remaining `Z`-blocks of the standard form (10.125): the
`r × r` block `B` in the top rows and the `r × k` block `C₂`. This file delivers the two reusable
`Z`-depositing gate primitives that network is built from; assembling them into (10.125) is the
final (assembly) development.

The two column operations these gates induce on the check matrix (`0 = I, 1 = X, 2 = Y, 3 = Z`;
symplectic bits `pauliXBit`/`pauliZBit` of `CliffordCSS/Symplectic/CheckMatrix.lean`) are the two ways to add a
`Z` without touching an `X`:

* **Phase gate `S` on wire `j`** — the column operation `z_j += x_j`: it sends `X ↦ Y` (`Y = XZ`
  adds a `Z`) and fixes `I, Z` (`phasePauli`, `CliffordCSS/Pauli/CliffordConjugation.lean`). On a
  row whose only `X` among the first `r` wires is on wire `j` (the `X`-identity block of (10.125)),
  `S_j` deposits a single `Z` on wire `j` — the **diagonal of `B`**.
* **Controlled-`Z` between wires `c, t`** — the symmetric column operation `z_c += x_t`,
  `z_t += x_c` (`X`-bits fixed). There is no primitive `CZ` gate in the elementary set
  `{H, S, CNOT}`, so it is realized as the three-gate circuit `CZ_{c,t} = H_t · CNOT_{c→t} · H_t`
  (`czGate`); its action is read off the existing Hadamard / CNOT tableaux. Between two top wires it
  builds the **off-diagonal of `B`**; between a top wire and an encoded wire it builds the block
  `C₂` (and, coupled through the top rows' `A₂`-block `X`-entries, the cross term of `B`).

## The phase layer

`sLayer ws` applies a phase gate to each wire in a list `ws` (`ws.map CliffordGate.phase`); the
gates commute and act on distinct wires, so it is a genuine *layer*. For distinct wires
(`ws.Nodup`):

* `act_sLayer` — its row action, `act (sLayer ws) g k = phasePauli (g k)` for `k ∈ ws`, else `g k`
  (only the chosen wires are transformed), mirroring `act_hadLayer`;
* `act_sLayer_xGenPauli` — the **diagonal-building layer**: on the pure-`X` generator `Xᵢ`,
  `act (sLayer ws) Xᵢ = Yᵢ` when `i ∈ ws`, else `Xᵢ` — the phase gate deposits a `Z` on wire `i`
  (`X ↦ Y`);
* `checkRow_act_sLayer_xGenPauli` — the same in check-matrix terms: row `i` becomes `(eᵢ | eᵢ)`
  (`X`- and `Z`-bit on wire `i`) for `i ∈ ws`, else `(eᵢ | 0)`;
* `sLayer_conj_xGenPauli` — the operator-level reading through the backbone
  `CliffordCircuit.conj_pauliString`: a unitary circuit conjugating `P_{Xᵢ}` to a nonzero (`±1`)
  multiple of `P_{Yᵢ}` / `P_{Xᵢ}`.

## The controlled-`Z` gate

`czGate c t h = [H_t, CNOT_{c→t}, H_t]` (with `h : c ≠ t`). Its check-matrix action is the pair
tableau `czCtrlPauli` / `czTgtPauli`, packaged as the string transformation `czPauliString`
(`act_czGate`), and its symplectic content is the CZ column operation:

* `pauliXBit_czCtrlPauli` / `pauliXBit_czTgtPauli` — the `X`-bits are unchanged;
* `pauliZBit_czCtrlPauli` (`z_c ↦ z_c + x_t`) / `pauliZBit_czTgtPauli` (`z_t ↦ z_t + x_c`) — each
  wire's `Z`-bit gains the *other* wire's `X`-bit, the symmetric hallmark of `CZ`;
* `czGate_conj_pauliString` — the operator-level reading through the backbone: a unitary circuit
  conjugating `P_g` to a nonzero (`±1`) multiple of `P_{czPauliString g c t}`.

Everything names only raw index / matrix data (`CliffordCSS.pauliString`, `CliffordCircuit`,
`Fin n → Fin 4`, `ZMod 2`). Assembling these layers with the Hadamard and CNOT layers into the
circuit carrying `G` (10.124) to the standard form (10.125) is the final development that reuses
this one.

## Design notes

* `czGate` introduces **no new `CliffordGate` constructor**: `CZ = H·CNOT·H` is a three-gate
  `CliffordCircuit`, so its `toMatrix`/`act`/`sign` are the existing folds and its conjugation is an
  instance of the backbone `CliffordCircuit.conj_pauliString` — the same discipline as the CNOT and
  Hadamard layers. `act_czGate` is proved by unfolding the three `Function.update`s of the
  composition (`had_t` acts, then `cnot`, then `had_t`), and the symplectic bit laws are a finite
  `Fin 4 × Fin 4` check (`decide`) against the composed Hadamard/CNOT tableaux.
* `act_sLayer` needs `ws.Nodup` for the same reason as `act_hadLayer`: although the clean statement
  is "transform exactly the wires in `ws`", the encoding circuit phases each chosen wire once. The
  `Nodup` is consumed only through the cons step `w ∉ ws`, so the outer `Function.update` reads the
  untouched value `g w`.
* `yGenPauli i` (`Y` on wire `i`) names the image of `Xᵢ` under `S_i`; its check row `(eᵢ | eᵢ)`
  (`checkRow_yGenPauli`) is the single diagonal entry of `B` that a phase gate deposits.
-/

open Matrix

namespace CliffordCSS

variable {n : ℕ}

/-! ### The `Y` generator (image of `Xᵢ` under a phase gate) -/

/-- The **pure-`Y` generator** `Yᵢ`: the Pauli string with `Y` on wire `i` and `I` on every other
wire (`Function.update 0 i 2`, using `0 = I`, `2 = Y`). It is the image of `Xᵢ` under a phase gate
on wire `i` (`act_sLayer_xGenPauli`); its check row is `(eᵢ | eᵢ)` (`checkRow_yGenPauli`), the
single diagonal `Z`-entry that a phase gate deposits on the `X`-identity block. -/
def yGenPauli (i : Fin n) : Fin n → Fin 4 := Function.update 0 i 2

@[simp] theorem yGenPauli_apply (i k : Fin n) : yGenPauli i k = if k = i then 2 else 0 := by
  simp only [yGenPauli, Function.update_apply, Pi.zero_apply]


/-! ### The phase (`S`) layer -/

/-- The **phase layer** on the wires `ws`: the Clifford circuit applying a phase gate `S` to each
wire in the list `ws` (`ws.map CliffordGate.phase`). With `ws` a set of top wires, this deposits the
diagonal `Z`-entries of the block `B` in the stabilizer encoding circuit of N&C Problem 10.3. -/
def sLayer (ws : List (Fin n)) : CliffordCircuit n := ws.map CliffordGate.phase

/-- The phase layer is built one wire at a time: `sLayer (w :: ws) = phase w :: sLayer ws`
(definitionally, `List.map` on a cons). -/
theorem sLayer_cons (w : Fin n) (ws : List (Fin n)) :
    sLayer (w :: ws) = CliffordGate.phase w :: sLayer ws := rfl

/-- **Row action of the phase layer.** For a list of **distinct** wires `ws`, conjugating a Pauli
string by `sLayer ws` applies the single-wire phase tableau `phasePauli` to exactly the wires in
`ws`, leaving the others fixed: `act (sLayer ws) g k = phasePauli (g k)` if `k ∈ ws`, else `g k`.
Proved by induction on `ws`; the cons step uses `w ∉ ws` (from `Nodup`) so the outer
`Function.update` on wire `w` reads the still-untouched value `g w`. -/
theorem act_sLayer (ws : List (Fin n)) (g : Fin n → Fin 4) (hnd : ws.Nodup) :
    CliffordCircuit.act (sLayer ws) g = fun k => if k ∈ ws then phasePauli (g k) else g k := by
  revert hnd
  induction ws with
  | nil => intro _; funext k; simp [sLayer, CliffordCircuit.act]
  | cons w ws ih =>
      intro hnd
      obtain ⟨hw, hnd'⟩ := List.nodup_cons.mp hnd
      have hrec := ih hnd'
      funext k
      rw [sLayer_cons]
      simp only [CliffordCircuit.act, CliffordGate.act]
      rw [hrec, Function.update_apply]
      rcases eq_or_ne k w with rfl | hk
      · simp [hw, List.mem_cons]
      · simp [hk, List.mem_cons]

/-! ### The phase layer as the diagonal-building layer of the encoding circuit -/


/-! ### The controlled-`Z` gate tableau -/

/-- The **new control Pauli** in `CZ_{c,t} (σ_a^c ⊗ σ_b^t) CZ_{c,t}†`, as a function of the control
index `a` and target index `b`. Since `CZ = H_t · CNOT_{c→t} · H_t`, it is the CNOT control Pauli
against the Hadamard-conjugated target: `czCtrlPauli a b = cnotCtrlPauli a (hadamardPauli b)`. Its
`X`-bit is unchanged and its `Z`-bit gains the target's `X`-bit (`pauliZBit_czCtrlPauli`). -/
def czCtrlPauli (a b : Fin 4) : Fin 4 := cnotCtrlPauli a (hadamardPauli b)

/-- The **new target Pauli** in `CZ_{c,t} (σ_a^c ⊗ σ_b^t) CZ_{c,t}†`. Conjugating the middle CNOT
target between two Hadamards on the target wire:
`czTgtPauli a b = hadamardPauli (cnotTgtPauli a (hadamardPauli b))`. Its `X`-bit is unchanged and
its `Z`-bit gains the control's `X`-bit (`pauliZBit_czTgtPauli`) — symmetric with the control, as
`CZ` is symmetric in its two wires. -/
def czTgtPauli (a b : Fin 4) : Fin 4 := hadamardPauli (cnotTgtPauli a (hadamardPauli b))


/-! ### The controlled-`Z` gate -/

/-- The **controlled-`Z` gate** between control wire `c` and target wire `t` (`h : c ≠ t`),
realized in the elementary gate set `{H, S, CNOT}` as `CZ_{c,t} = H_t · CNOT_{c→t} · H_t` — the
three-gate Clifford circuit `[had t, cnot c t, had t]` (the head `had t` is applied last). Its
check-matrix action is the symmetric column operation `z_c += x_t`, `z_t += x_c` (`act_czGate`,
the bit laws `pauliZBit_cz…`). -/
def czGate (c t : Fin n) (h : c ≠ t) : CliffordCircuit n :=
  [CliffordGate.had t, CliffordGate.cnot c t h, CliffordGate.had t]

/-- The **controlled-`Z`-transformed Pauli string**: `CZ_{c,t}` conjugation changes only wire `c`
(to `czCtrlPauli (g c) (g t)`) and wire `t` (to `czTgtPauli (g c) (g t)`), leaving every other wire
fixed. Both new Paulis depend on the *original* pair `(g c, g t)`. -/
def czPauliString (g : Fin n → Fin 4) (c t : Fin n) : Fin n → Fin 4 :=
  Function.update (Function.update g t (czTgtPauli (g c) (g t))) c (czCtrlPauli (g c) (g t))

/-- The `CZ`-transformed string on the control wire:
`czPauliString g c t c = czCtrlPauli (g c) (g t)`. -/
@[simp] theorem czPauliString_ctrl (g : Fin n → Fin 4) (c t : Fin n) :
    czPauliString g c t c = czCtrlPauli (g c) (g t) :=
  Function.update_self ..

/-- The `CZ`-transformed string on the target wire: `czPauliString g c t t = czTgtPauli (g c) (g t)`
(needs `c ≠ t`). -/
theorem czPauliString_tgt (g : Fin n → Fin 4) {c t : Fin n} (h : c ≠ t) :
    czPauliString g c t t = czTgtPauli (g c) (g t) := by
  simp only [czPauliString, Function.update_of_ne h.symm, Function.update_self]

/-- The `CZ`-transformed string off wires `c` and `t` is unchanged: `czPauliString g c t k = g k`
for `k ≠ c`, `k ≠ t`. -/
theorem czPauliString_of_ne (g : Fin n → Fin 4) (c t : Fin n) {k : Fin n} (hkc : k ≠ c)
    (hkt : k ≠ t) : czPauliString g c t k = g k := by
  simp only [czPauliString, Function.update_of_ne hkc, Function.update_of_ne hkt]

/-- **Row action of the controlled-`Z` gate.** Conjugating a Pauli string by `czGate c t h` applies
the pair tableau `czCtrlPauli` / `czTgtPauli` to wires `c, t` and fixes the rest:
`act (czGate c t h) g = czPauliString g c t`. Proved by unfolding the three `Function.update`s of
the composition `H_t · CNOT_{c→t} · H_t` (the inner Hadamard acts first, then the CNOT column
operation, then the outer Hadamard) and reading the resulting wire values. -/
theorem act_czGate (c t : Fin n) (h : c ≠ t) (g : Fin n → Fin 4) :
    CliffordCircuit.act (czGate c t h) g = czPauliString g c t := by
  funext k
  simp only [czGate, CliffordCircuit.act, CliffordGate.act, czPauliString, czTgtPauli, czCtrlPauli]
  rcases eq_or_ne k c with rfl | hkc
  · rw [Function.update_self, Function.update_of_ne h, cnotPauliString_ctrl,
      Function.update_of_ne h, Function.update_self]
  · rw [Function.update_of_ne hkc]
    rcases eq_or_ne k t with rfl | hkt
    · rw [Function.update_self, Function.update_self, cnotPauliString_tgt _ h,
        Function.update_self, Function.update_of_ne h]
    · rw [Function.update_of_ne hkt, Function.update_of_ne hkt,
        cnotPauliString_of_ne _ _ _ hkc hkt, Function.update_of_ne hkt]


end CliffordCSS

import CliffordCSS.Pauli.CnotConjugation

/-!
# A Clifford circuit conjugates a Pauli string to a Pauli string (encoding backbone)

This file is pure mathematics : it packages the single-wire
Hadamard/phase gates of `CliffordCSS/Pauli/CliffordConjugation.lean` and the two-wire `CNOT` gate
of `CliffordCSS/Pauli/CnotConjugation.lean` into a **Clifford circuit** — a finite sequence of
these gates — and proves the fact those files were built for: conjugating an `n`-qubit Pauli string
(`CliffordCSS.pauliString`, `g : Fin n → Fin 4`) by a Clifford circuit returns another Pauli string, up
to a nonzero (`±1`) phase, whose **check matrix** is obtained from `g`'s by applying, in order, each
gate's elementary symplectic column operation. This is the operator-level statement of Nielsen &
Chuang **Problem 10.3**: *a circuit acts on the check matrix by column operations*, and the encoding
circuit of Eqs (10.124)→(10.125) is exactly such a sequence. The concrete `(10.124)→(10.125)`
synthesis is a later development that invokes this backbone.

Everything names only raw matrix / index data (`Matrix`, `CliffordCSS.pauliString`, `Fin n → Fin 4`,
`Fin n → Fin 2`).

## The gate and circuit

`CliffordGate n` is the elementary gate set: `had j` and `phase j` (the single-wire Hadamard/phase
gates on wire `j`) and `cnot c t (h : c ≠ t)` (the two-wire controlled-NOT with control `c`, target
`t`). Three data are read off a gate:

* `CliffordGate.toMatrix` — its unitary matrix (`kronWireGate j hadamardC` /
  `kronWireGate j sMatrix` / `cnotWireGate c t`);
* `CliffordGate.act` — its **phase-free action** on a Pauli string, i.e. how it transforms the
  check-matrix row (`Function.update` via `hadamardPauli` / `phasePauli`, or `cnotPauliString`);
* `CliffordGate.sign` — the `±1` phase acquired under conjugation (`hadamardPauliSign` /
  `phasePauliSign` / `cnotPauliSign`), discarded by the check matrix but tracked here for the exact
  operator identity.

A `CliffordCircuit n` is a `List (CliffordGate n)`, read right-to-left: `(γ :: U).toMatrix =
γ.toMatrix * U.toMatrix` applies `U` first then `γ`, with `act`/`sign` the matching folds.

## What is proved

* `CliffordGate.conj` / `CliffordGate.mul_conjTranspose` — the single-gate conjugation
  `γ.toMatrix · P_g · γ.toMatrixᴴ = γ.sign g • P_{γ.act g}` (unifying the three per-gate theorems)
  and gate unitarity `γ.toMatrix · γ.toMatrixᴴ = 1`.
* `CliffordCircuit.conj_pauliString` — **the backbone**: for any circuit `U`,
  `U.toMatrix · P_g · U.toMatrixᴴ = U.sign g • P_{U.act g}`. By induction on the gate list: the cons
  case is `(γ M) P (γ M)ᴴ = γ (M P Mᴴ) γᴴ` (associativity + `conjTranspose_mul`), the inductive
  hypothesis on the inner conjugation, and one application of `CliffordGate.conj`, collecting
  the two `±1` scalars.
* `CliffordCircuit.mul_conjTranspose` — a Clifford circuit is **unitary** (`U.toMatrix · U.toMatrixᴴ
  = 1`), from gate unitarity by the same induction.
* `CliffordGate.sign_ne_zero` / `CliffordCircuit.sign_ne_zero` — the conjugation phase is nonzero
  (each gate phase is `±1`, a circuit's is a product of them), so `U` conjugates `P_g` to a genuine
  scalar multiple of `P_{U.act g}` — it is never annihilated.

## Design notes

* The carrier is the **phase-free** `pauliString`, matching the whole Chapter-10 stabilizer program:
  the check matrix records a Pauli only up to phase, so the `±1` signs live in `sign`, never in
  `act`. Nielsen & Chuang fix the signs of the encoded generators separately (Proposition 10.4), so
  the phase-free `act` is the right notion of "the circuit's action on the check matrix".
* `CliffordCircuit.sign (γ :: U) g` is defined as `U.sign g * γ.sign (U.act g)` — the order in which
  `smul_smul` collects the scalars in the `conj_pauliString` induction — so no `mul_comm` is needed;
  conceptually the order is immaterial (`ℂ` is commutative).
* No unitarity is used in `conj_pauliString`: conjugation composes for *any* matrices. Unitarity
  is a separate deliverable: a Clifford circuit is a genuine gate of a quantum circuit.
-/

open Matrix

noncomputable section

namespace CliffordCSS

variable {n : ℕ}

/-! ### `±1`-valued gate signs are nonzero -/

/-- The Hadamard conjugation sign is nonzero (`±1`): `hadamardPauliSign a ≠ 0` for every `a`. -/
private theorem hadamardPauliSign_ne_zero (a : Fin 4) : hadamardPauliSign a ≠ 0 := by
  fin_cases a <;> simp [hadamardPauliSign]

/-- The phase-gate conjugation sign is nonzero (`±1`): `phasePauliSign a ≠ 0` for every `a`. -/
private theorem phasePauliSign_ne_zero (a : Fin 4) : phasePauliSign a ≠ 0 := by
  fin_cases a <;> simp [phasePauliSign]

/-- The CNOT conjugation sign is nonzero (`±1`): `cnotPauliSign a b ≠ 0` for every pair `a, b`. -/
private theorem cnotPauliSign_ne_zero (a b : Fin 4) : cnotPauliSign a b ≠ 0 := by
  fin_cases a <;> fin_cases b <;> simp [cnotPauliSign]

/-! ### Clifford gates -/

/-- An **elementary Clifford gate** on the `n`-qubit register: the single-wire Hadamard (`had j`)
and phase (`phase j`) gates on wire `j`, and the two-wire controlled-NOT (`cnot c t h`) with control
`c`, target `t` (`h : c ≠ t`). These are the generators of the check-matrix column operations behind
the encoding circuit of Nielsen & Chuang Problem 10.3. -/
inductive CliffordGate (n : ℕ) where
  /-- The Hadamard gate on wire `j`. -/
  | had (j : Fin n)
  /-- The phase gate `S` on wire `j`. -/
  | phase (j : Fin n)
  /-- The controlled-NOT gate with control wire `c` and target wire `t` (`c ≠ t`). -/
  | cnot (c t : Fin n) (h : c ≠ t)

namespace CliffordGate

/-- The **unitary matrix** of an elementary Clifford gate: `kronWireGate j hadamardC` for `had j`,
`kronWireGate j sMatrix` for `phase j`, and `cnotWireGate c t` for `cnot c t`. -/
def toMatrix : CliffordGate n → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | .had j => kronWireGate j hadamardC
  | .phase j => kronWireGate j sMatrix
  | .cnot c t _ => cnotWireGate c t

/-- The **phase-free action** of an elementary Clifford gate on a Pauli string `g : Fin n → Fin 4`,
i.e. how it transforms the check-matrix row: the Hadamard/phase gates update wire `j` by
`hadamardPauli` / `phasePauli`, and `cnot c t` applies `cnotPauliString`. -/
def act : CliffordGate n → (Fin n → Fin 4) → (Fin n → Fin 4)
  | .had j, g => Function.update g j (hadamardPauli (g j))
  | .phase j, g => Function.update g j (phasePauli (g j))
  | .cnot c t _, g => cnotPauliString g c t

/-- The **`±1` phase** an elementary Clifford gate acquires when conjugating the Pauli string `g`:
`hadamardPauliSign (g j)` / `phasePauliSign (g j)` for the single-wire gates and
`cnotPauliSign (g c) (g t)` for `cnot c t`. Discarded by the check matrix but tracked here for
the exact operator identity `CliffordGate.conj`. -/
def sign : CliffordGate n → (Fin n → Fin 4) → ℂ
  | .had j, g => hadamardPauliSign (g j)
  | .phase j, g => phasePauliSign (g j)
  | .cnot c t _, g => cnotPauliSign (g c) (g t)

/-- **Single-gate conjugation.** Conjugating a Pauli string `P_g` by an elementary Clifford gate
returns the Pauli string `P_{γ.act g}` up to the `±1` phase `γ.sign g`:
`γ.toMatrix · P_g · γ.toMatrixᴴ = γ.sign g • P_{γ.act g}`. This unifies the three per-gate theorems
`hadamardWire_conj_pauliString`, `phaseWire_conj_pauliString`, `cnotWireGate_conj_pauliString`. -/
theorem conj (γ : CliffordGate n) (g : Fin n → Fin 4) :
    γ.toMatrix * pauliString g * γ.toMatrixᴴ = γ.sign g • pauliString (γ.act g) := by
  cases γ with
  | had j => exact hadamardWire_conj_pauliString j g
  | phase j => exact phaseWire_conj_pauliString j g
  | cnot c t h => exact cnotWireGate_conj_pauliString c t h g

/-- An elementary Clifford gate is **unitary**: `γ.toMatrix · γ.toMatrixᴴ = 1`. For the single-wire
gates via `kronWireGate_mul_conjTranspose` (`hadamardC` Hermitian involution; `sMatrix` in the
unitary group); for `cnot` via `cnotWireGate_mul_conjTranspose`. -/
theorem mul_conjTranspose (γ : CliffordGate n) : γ.toMatrix * γ.toMatrixᴴ = 1 := by
  cases γ with
  | had j =>
      exact kronWireGate_mul_conjTranspose
        (by rw [hadamardC_isHermitian]; exact hadamardC_mul_self) j
  | phase j =>
      exact kronWireGate_mul_conjTranspose
        (Matrix.mem_unitaryGroup_iff.mp sMatrix_mem_unitaryGroup) j
  | cnot c t h => exact cnotWireGate_mul_conjTranspose c t h

/-- The single-gate conjugation phase is **nonzero** (`±1`): `γ.sign g ≠ 0`. -/
theorem sign_ne_zero (γ : CliffordGate n) (g : Fin n → Fin 4) : γ.sign g ≠ 0 := by
  cases γ with
  | had j => exact hadamardPauliSign_ne_zero (g j)
  | phase j => exact phasePauliSign_ne_zero (g j)
  | cnot c t _ => exact cnotPauliSign_ne_zero (g c) (g t)

end CliffordGate

/-! ### Clifford circuits -/

/-- A **Clifford circuit** on the `n`-qubit register: a finite sequence of elementary Clifford gates
(`CliffordGate n`). Read right-to-left: the head gate is applied last (see `toMatrix`). -/
abbrev CliffordCircuit (n : ℕ) := List (CliffordGate n)

namespace CliffordCircuit

/-- The **unitary matrix** of a Clifford circuit: the product of its gate matrices, with the head
applied last — `[].toMatrix = 1`, `(γ :: U).toMatrix = γ.toMatrix * U.toMatrix`. -/
def toMatrix : CliffordCircuit n → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | [] => 1
  | γ :: U => γ.toMatrix * toMatrix U

/-- The **phase-free action** of a Clifford circuit on a Pauli string (its transformation of the
check-matrix row): apply the gates right-to-left — `[].act g = g`, `(γ :: U).act g = γ.act (U.act
g)`. This is the composed sequence of elementary symplectic column operations. -/
def act : CliffordCircuit n → (Fin n → Fin 4) → (Fin n → Fin 4)
  | [], g => g
  | γ :: U, g => γ.act (act U g)

/-- The **`±1` phase** a Clifford circuit acquires conjugating `P_g`: the product of the per-gate
phases along the fold — `[].sign g = 1`, `(γ :: U).sign g = U.sign g * γ.sign (U.act g)` (the inner
circuit `U` acts first, so its phase multiplies the head gate's phase at the intermediate string
`U.act g`). -/
def sign : CliffordCircuit n → (Fin n → Fin 4) → ℂ
  | [], _ => 1
  | γ :: U, g => sign U g * γ.sign (act U g)

/-- **The backbone (Nielsen & Chuang Problem 10.3): a Clifford circuit conjugates a Pauli string to
a Pauli string.** For any circuit `U` and Pauli string `g`,
`U.toMatrix · P_g · U.toMatrixᴴ = U.sign g • P_{U.act g}`: `U` maps `P_g` to the Pauli string
`P_{U.act g}` — whose check matrix is `g`'s after the composed column operations — up to the `±1`
phase `U.sign g`. This is the precise sense in which *a Clifford circuit acts on the check matrix by
column operations*.

By induction on the gate list. The cons case rewrites `(γ.toMatrix * U.toMatrix) · P_g ·
(γ.toMatrix * U.toMatrix)ᴴ` to `γ.toMatrix · (U.toMatrix · P_g · U.toMatrixᴴ) · γ.toMatrixᴴ`
(`conjTranspose_mul` + associativity), applies the inductive hypothesis to the inner conjugation,
then `CliffordGate.conj` to the outer gate, collecting the two `±1` scalars via `smul_smul`. -/
theorem conj_pauliString (U : CliffordCircuit n) (g : Fin n → Fin 4) :
    toMatrix U * pauliString g * (toMatrix U)ᴴ = sign U g • pauliString (act U g) := by
  induction U with
  | nil => simp [toMatrix, act, sign]
  | cons γ U ih =>
      change (γ.toMatrix * toMatrix U) * pauliString g * (γ.toMatrix * toMatrix U)ᴴ
          = sign (γ :: U) g • pauliString (act (γ :: U) g)
      rw [Matrix.conjTranspose_mul,
        show (γ.toMatrix * toMatrix U) * pauliString g * ((toMatrix U)ᴴ * γ.toMatrixᴴ)
            = γ.toMatrix * (toMatrix U * pauliString g * (toMatrix U)ᴴ) * γ.toMatrixᴴ from by
          simp only [Matrix.mul_assoc],
        ih, mul_smul_comm, smul_mul_assoc, γ.conj, smul_smul]
      simp only [sign, act]

/-- A Clifford circuit is **unitary**: `U.toMatrix · U.toMatrixᴴ = 1`. By induction on the gate list
from single-gate unitarity `CliffordGate.mul_conjTranspose`: the cons case reassociates
`(γ M) (γ M)ᴴ = γ (M Mᴴ) γᴴ`, uses the inductive hypothesis `M Mᴴ = 1`, then the head gate's
unitarity. -/
theorem mul_conjTranspose (U : CliffordCircuit n) : toMatrix U * (toMatrix U)ᴴ = 1 := by
  induction U with
  | nil => simp [toMatrix]
  | cons γ U ih =>
      change (γ.toMatrix * toMatrix U) * (γ.toMatrix * toMatrix U)ᴴ = 1
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (toMatrix U), ih,
        Matrix.one_mul]
      exact γ.mul_conjTranspose

/-- The Clifford-circuit conjugation phase is **nonzero**: `U.sign g ≠ 0`, since it is a product of
the `±1` per-gate phases (`CliffordGate.sign_ne_zero`). Hence `U` conjugates `P_g` to a genuine
scalar multiple of `P_{U.act g}` — never to `0`. -/
theorem sign_ne_zero (U : CliffordCircuit n) (g : Fin n → Fin 4) : sign U g ≠ 0 := by
  induction U with
  | nil => simp [sign]
  | cons γ U ih => exact mul_ne_zero ih (γ.sign_ne_zero (act U g))

/-! ### Composition of Clifford circuits (list append)

Since a `CliffordCircuit` is a gate list, `U ++ V` is the circuit that runs `V` first then `U`
(matching `toMatrix`'s right-to-left reading). These three lemmas record how the matrix, the
phase-free action, and the `±1` phase compose across an append — the algebra any *synthesis* of a
circuit from smaller pieces relies on (e.g. the inductive construction of Nielsen & Chuang
Exercise 10.40, which glues a permutation-fixing sub-circuit to a sign-fixing one). -/

/-- **The matrix of an appended circuit is the product of the matrices**: `(U ++ V).toMatrix =
U.toMatrix · V.toMatrix`, so `V` acts first (rightmost). By induction on the gate list `U`. -/
theorem toMatrix_append (U V : CliffordCircuit n) :
    toMatrix (U ++ V) = toMatrix U * toMatrix V := by
  induction U with
  | nil => simp [toMatrix]
  | cons γ U ih => simp only [List.cons_append, toMatrix, ih, Matrix.mul_assoc]

/-- **The action of an appended circuit is the composed action**: `(U ++ V).act g = U.act (V.act
g)`, `V` acting first. By induction on the gate list `U`. -/
theorem act_append (U V : CliffordCircuit n) (g : Fin n → Fin 4) :
    act (U ++ V) g = act U (act V g) := by
  induction U with
  | nil => rfl
  | cons γ U ih => simp only [List.cons_append, act, ih]

/-- **The phase of an appended circuit multiplies across the join**: `(U ++ V).sign g = V.sign g ·
U.sign (V.act g)` — `V`'s phase at `g`, times `U`'s phase at the intermediate string `V.act g`.
By induction on the gate list `U`, using `act_append` for the intermediate string. -/
theorem sign_append (U V : CliffordCircuit n) (g : Fin n → Fin 4) :
    sign (U ++ V) g = sign V g * sign U (act V g) := by
  induction U with
  | nil => simp [sign]
  | cons γ U ih =>
      simp only [List.cons_append, sign, act_append, ih]
      ring

end CliffordCircuit

/-! ### Relabeling a Clifford circuit along a wire embedding

A Clifford circuit on `m` wires transports onto `n` wires along an **injection of wires**
`f : Fin m ↪ Fin n`, relabeling each gate's wires by `f` (`had j ↦ had (f j)`, `cnot c t ↦
cnot (f c) (f t)`, …). On the embedded wires the transported circuit acts exactly as the original:
its phase-free action and `±1` phase **pull back** along `f`
(`CliffordCircuit.act_relabel_comp`, `CliffordCircuit.sign_relabel`), and every wire *outside* the
range of `f` is left untouched (`CliffordCircuit.act_relabel_of_forall_ne`). Concretely, writing
`g ∘ f` for the string `k ↦ g (f k)` read off the embedded wires,
`(C.relabel f).act g (f i) = C.act (g ∘ f) i` and `(C.relabel f).sign g = C.sign (g ∘ f)`.

This is the mechanism by which the inductive Clifford synthesis of Nielsen & Chuang Exercise 10.40
embeds the `n`-qubit inductive hypothesis into a sub-register of an `(n+1)`-qubit register (the
embedding `f` picking out the sub-register's wires), and runs the single-qubit base case on any
chosen wire (`f = fun _ => j` on `Fin 1 ↪ Fin n`). Because a relabeled circuit is a genuine
Clifford circuit, its conjugation of Pauli strings is again governed by `conj_pauliString`, now with
the pulled-back action/sign. -/

variable {m : ℕ}

/-- **Relabel an elementary Clifford gate's wires along `f : Fin m ↪ Fin n`.** `had j ↦ had (f j)`,
`phase j ↦ phase (f j)`, and `cnot c t ↦ cnot (f c) (f t)` — the target/control distinctness `c ≠ t`
is preserved because `f` is injective. -/
def CliffordGate.relabel (f : Fin m ↪ Fin n) : CliffordGate m → CliffordGate n
  | .had j => .had (f j)
  | .phase j => .phase (f j)
  | .cnot c t h => .cnot (f c) (f t) fun he => h (f.injective he)

/-- **On an embedded wire `f i`, a relabeled gate acts as the original gate on the pulled-back
string** `k ↦ g (f k)`: `(γ.relabel f).act g (f i) = γ.act (fun k => g (f k)) i`. The single-wire
gates update only their (relabeled) wire; injectivity of `f` matches the off-wire indices, and for
`cnot` the control/target/rest split of `cnotPauliString` transports through `f`. -/
theorem CliffordGate.act_relabel_embed (f : Fin m ↪ Fin n) (γ : CliffordGate m)
    (g : Fin n → Fin 4) (i : Fin m) :
    (γ.relabel f).act g (f i) = γ.act (fun k => g (f k)) i := by
  cases γ with
  | had j =>
      simp only [CliffordGate.relabel, CliffordGate.act]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne (f.injective.ne hij), Function.update_of_ne hij]
  | phase j =>
      simp only [CliffordGate.relabel, CliffordGate.act]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne (f.injective.ne hij), Function.update_of_ne hij]
  | cnot c t h =>
      simp only [CliffordGate.relabel, CliffordGate.act]
      by_cases hic : i = c
      · subst hic; rw [cnotPauliString_ctrl, cnotPauliString_ctrl]
      · by_cases hit : i = t
        · subst hit
          rw [cnotPauliString_tgt g (f.injective.ne h), cnotPauliString_tgt _ h]
        · rw [cnotPauliString_of_ne g (f c) (f t) (f.injective.ne hic) (f.injective.ne hit),
            cnotPauliString_of_ne _ c t hic hit]

/-- **A relabeled gate leaves every wire outside the range of `f` untouched**: if `f i ≠ k` for all
`i`, then `(γ.relabel f).act g k = g k`. A relabeled gate only ever touches wires in `f`'s range. -/
theorem CliffordGate.act_relabel_of_forall_ne (f : Fin m ↪ Fin n) (γ : CliffordGate m)
    (g : Fin n → Fin 4) {k : Fin n} (hk : ∀ i, f i ≠ k) :
    (γ.relabel f).act g k = g k := by
  cases γ with
  | had j =>
      simp only [CliffordGate.relabel, CliffordGate.act, Function.update_of_ne (hk j).symm]
  | phase j =>
      simp only [CliffordGate.relabel, CliffordGate.act, Function.update_of_ne (hk j).symm]
  | cnot c t h =>
      simp only [CliffordGate.relabel, CliffordGate.act]
      rw [cnotPauliString_of_ne g (f c) (f t) (hk c).symm (hk t).symm]

/-- **A relabeled gate's `±1` phase pulls back along `f`**: `(γ.relabel f).sign g =
γ.sign (fun k => g (f k))`. Each gate's phase depends only on the (relabeled) wire values, so it is
unchanged by reading the string through `f`. -/
theorem CliffordGate.sign_relabel (f : Fin m ↪ Fin n) (γ : CliffordGate m) (g : Fin n → Fin 4) :
    (γ.relabel f).sign g = γ.sign (fun k => g (f k)) := by
  cases γ <;> rfl

namespace CliffordCircuit

/-- **Relabel a Clifford circuit's wires along `f : Fin m ↪ Fin n`**, gate by gate
(`CliffordGate.relabel`). -/
def relabel (f : Fin m ↪ Fin n) (C : CliffordCircuit m) : CliffordCircuit n :=
  C.map (CliffordGate.relabel f)

/-- **A relabeled Clifford circuit acts, on the embedded wires, as the original on the pulled-back
string** — as a full function equality: `(fun i => (relabel f C).act g (f i)) = C.act (fun k =>
g (f k))`. By induction on the gate list from the single-gate pullback
`CliffordGate.act_relabel_embed`. This is the key identity letting the inductive synthesis of
Exercise 10.40 reuse a sub-register circuit on a chosen set of wires. -/
theorem act_relabel_comp (f : Fin m ↪ Fin n) (C : CliffordCircuit m) (g : Fin n → Fin 4) :
    (fun i => act (relabel f C) g (f i)) = act C (fun k => g (f k)) := by
  induction C generalizing g with
  | nil => rfl
  | cons γ C ih =>
      funext i
      change (γ.relabel f).act (act (relabel f C) g) (f i) = γ.act (act C (fun k => g (f k))) i
      rw [CliffordGate.act_relabel_embed, ih g]

/-- **The embedded-wire action, pointwise**: `(relabel f C).act g (f i) = C.act (fun k => g (f k))
i` for every `i`. The pointwise form of `act_relabel_comp`. -/
theorem act_relabel_embed (f : Fin m ↪ Fin n) (C : CliffordCircuit m)
    (g : Fin n → Fin 4) (i : Fin m) :
    act (relabel f C) g (f i) = act C (fun k => g (f k)) i :=
  congrFun (act_relabel_comp f C g) i

/-- **A relabeled Clifford circuit leaves every wire outside the range of `f` untouched**: if
`f i ≠ k` for all `i`, then `(relabel f C).act g k = g k`. By induction from the single-gate
version `CliffordGate.act_relabel_of_forall_ne`; this lets the induction embed a sub-register
circuit without disturbing the qubits it peels off. -/
theorem act_relabel_of_forall_ne (f : Fin m ↪ Fin n) (C : CliffordCircuit m)
    (g : Fin n → Fin 4) {k : Fin n} (hk : ∀ i, f i ≠ k) :
    act (relabel f C) g k = g k := by
  induction C generalizing g with
  | nil => rfl
  | cons γ C ih =>
      change (γ.relabel f).act (act (relabel f C) g) k = g k
      rw [CliffordGate.act_relabel_of_forall_ne f γ _ hk, ih g]

/-- **A relabeled Clifford circuit's `±1` phase pulls back along `f`**: `(relabel f C).sign g =
C.sign (fun k => g (f k))`. By induction on the gate list, using the single-gate phase pullback
`CliffordGate.sign_relabel` and the action pullback `act_relabel_comp` for the intermediate string.
Together with `act_relabel_embed`, a relabeled circuit realises on the embedded wires exactly the
signed permutation of the original — the transport of a sub-register synthesis into the full
register. -/
theorem sign_relabel (f : Fin m ↪ Fin n) (C : CliffordCircuit m) (g : Fin n → Fin 4) :
    sign (relabel f C) g = sign C (fun k => g (f k)) := by
  induction C generalizing g with
  | nil => rfl
  | cons γ C ih =>
      change sign (relabel f C) g * (γ.relabel f).sign (act (relabel f C) g)
        = sign C (fun k => g (f k)) * γ.sign (act C (fun k => g (f k)))
      rw [ih g, CliffordGate.sign_relabel, act_relabel_comp]

end CliffordCircuit

end CliffordCSS

end

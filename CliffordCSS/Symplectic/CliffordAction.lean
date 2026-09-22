import CliffordCSS.DepthOne.ShearLevi
import CliffordCSS.Normalizer.Symplectic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.ZMod

/-!
# A Clifford circuit acts on Pauli labels by a binary symplectic matrix

Pure mathematics : the bridge between the library's **Clifford
layer** (`CliffordCSS/Pauli/CliffordCircuit.lean`: `CliffordCircuit n` and its phase-free action
`CliffordCircuit.act` on Pauli-index strings) and its **binary symplectic layer**
(`CliffordCSS/Symplectic/CheckMatrixSymplectic.lean` / `CliffordCSS/Symplectic/Group.lean`: the check vector
`checkVec`, the Gram matrix `Λ = symplecticMatrix`, and `binarySymplecticGroup`). This is
Gottesman's classical fact, the engine of the stabilizer formalism:

> conjugating a Pauli operator by a Clifford unitary acts **linearly and symplectically** on its
> `(x | z)` label.

Both layers existed; nothing connected them. This file supplies the connection.

## The action on labels

A Clifford circuit `U` conjugates a Pauli string to a Pauli string up to a `±1` phase,
`U P_g U† = sign U g • P_{act U g}` (`CliffordCircuit.conj_pauliString`), so it induces a map on
*labels*: `checkVec g ↦ checkVec (act U g)`. Two facts make this a symplectic matrix.

* **Well-definedness and linearity.** The label map `checkVec` is a bijection from Pauli-index
  strings onto `𝔽₂^{2n}` (`checkVecEquiv`, in `CliffordCSS/Symplectic/CheckMatrixSymplectic.lean`), and it
  carries the Pauli-index product to addition (`checkVec_pauliMulIndex`). The phase-free action is
  a *group* map for that product,
  `act U (g ⊙ h) = act U g ⊙ act U h` (`CliffordCircuit.act_pauliMulIndex`, from the per-gate
  tableau identities `hadamardPauli_pauliMul`, `phasePauli_pauliMul`, `cnotCtrlPauli_pauliMul`,
  `cnotTgtPauli_pauliMul`). Transporting along the bijection therefore gives an **additive** —
  hence, over `𝔽₂`, `ZMod 2`-**linear** — endomorphism `cliffordLabelMap U` of `𝔽₂^{2n}`.
* **Symplecticity.** Two Pauli strings commute iff their labels pair trivially under `Λ`
  (Nielsen & Chuang Exercise 10.33, `pauliString_commute_iff_symplecticForm`), and conjugation by a
  unitary preserves commutation — the pre-existing
  `CliffordCircuit.act_pauliAnticommCount_even_iff`. So the label map preserves the symplectic form
  (`symplecticForm_checkVec_act`), and its matrix lies in `binarySymplecticGroup`.

## What is proved

* `CliffordGate.act_pauliMulIndex` / `CliffordCircuit.act_pauliMulIndex` — **the phase-free Clifford
  action is multiplicative on Pauli indices**: `act U (g ⊙ h) = act U g ⊙ act U h`.
* `cliffordLabelMap` — **the `𝔽₂`-linear label action** of a Clifford circuit, with
  `cliffordLabelMap_checkVec : cliffordLabelMap U (checkVec g) = checkVec (act U g)`.
* `cliffordSymplectic` — **the symplectic matrix of a Clifford circuit**, acting on labels as row
  vectors from the right (`checkVec_act : checkVec (act U g) = checkVec g ᵥ* cliffordSymplectic U`),
  with entries `cliffordSymplectic_apply`.
* `cliffordSymplectic_mem_binarySymplecticGroup` — **the headline**:
  `cliffordSymplectic U ∈ Sp(2n, 𝔽₂)`, an application of the general form-side criterion
  `mem_binarySymplecticGroup_iff_symplecticForm_vecMul` (`CliffordCSS/Symplectic/Group.lean`).
* `cliffordLabelMap_phase` / `cliffordSymplectic_phase` — a worked generator: the phase gate on
  wire `j` acts as, and so has matrix, the `Z`-shear `shearZ (single j j 1)` — one of the three
  families of *Beyond transversality*, App. D.
* `cliffordSymplectic_nil` / `cliffordSymplectic_append` — **functoriality**: the empty circuit
  gives `1`, and `cliffordSymplectic (U ++ V) = cliffordSymplectic V * cliffordSymplectic U`.

## Design notes

* **Index convention.** Labels are indexed by `Fin n ⊕ Fin n` (`inl` = `X`-part, `inr` = `Z`-part),
  the convention already fixed by `checkVec` and by `binarySymplecticGroup`'s `ι ⊕ ι`, so no
  re-indexing is needed anywhere.
* **Action convention.** Labels are **row** vectors acted on from the **right** by `Matrix.vecMul`,
  matching Convention c2 of *Beyond transversality* (`vecMul_fromBlocks_blocks`). Consequently
  `cliffordSymplectic` is an *anti*-homomorphism from circuit composition:
  `cliffordSymplectic (U ++ V) = cliffordSymplectic V * cliffordSymplectic U`, since in `U ++ V` the
  circuit `V` acts first (`CliffordCircuit.act_append`) and so its matrix must multiply first from
  the left of a row vector. Concretely `cliffordSymplectic U := (LinearMap.toMatrix' …)ᵀ`: Mathlib's
  `toMatrix'` is set up for the column action `mulVec`, and the transpose converts it to the row
  action.
* **Shared pieces live upstream.** The label bijection `checkVecEquiv` / `vecPauli` and
  `checkVec_pauliMulIndex` sit with `checkVec` in `CliffordCSS/Symplectic/CheckMatrixSymplectic.lean`; its
  single-qubit ingredients `bitToPauli_pauliBit` / `bitToPauli_add` sit with `bitToPauli` in
  `CliffordCSS/Encoding/StabilizerGeneratorFlip.lean`; the form-side membership criterion sits with the group in
  `CliffordCSS/Symplectic/Group.lean`. This file contains only the Clifford-specific content.
* **Definition by transport, not by gates.** `cliffordSymplectic` is defined from the linear map,
  not as a product of explicit per-gate matrices. This makes linearity, functoriality and
  symplecticity single applications of the corresponding facts about `act`, with no block-matrix
  computation; the explicit gate matrices (Hadamard = the `X`/`Z` swap on one wire, phase gate =
  a `shearZ`, CNOT = a transvection pair) are recoverable entrywise from
  `cliffordSymplectic_apply`; `cliffordSymplectic_phase` works one of them out (the phase gate is
  exactly a `shearZ`), and the other two are deliberately deferred.

Everything here names only raw matrix / index data (`Matrix`, `CliffordCSS.CliffordCircuit`,
`CliffordCSS.checkVec`, `Fin n → Fin 4`, `ZMod 2`).
-/

open Matrix

namespace CliffordCSS

variable {n : ℕ}

/-! ### The phase-free Clifford action is multiplicative on Pauli indices -/

/-- The Hadamard tableau is **multiplicative**: `H (a ⊙ b) = (H a) ⊙ (H b)`, where `H` is the
single-qubit conjugation tableau `hadamardPauli`. A `16`-case check; the one-qubit instance of
`CliffordGate.act_pauliMulIndex` for `had`. -/
theorem hadamardPauli_pauliMul (a b : Fin 4) :
    hadamardPauli (pauliMul a b) = pauliMul (hadamardPauli a) (hadamardPauli b) := by decide +revert

/-- The phase-gate tableau is **multiplicative**: `S (a ⊙ b) = (S a) ⊙ (S b)` for the single-qubit
conjugation tableau `phasePauli`. A `16`-case check. -/
theorem phasePauli_pauliMul (a b : Fin 4) :
    phasePauli (pauliMul a b) = pauliMul (phasePauli a) (phasePauli b) := by decide +revert

/-- The CNOT **control** tableau is multiplicative in both arguments simultaneously:
`ctrl (a ⊙ a') (b ⊙ b') = ctrl a b ⊙ ctrl a' b'`. A `256`-case check; with `cnotTgtPauli_pauliMul`
it is the two-qubit instance of `CliffordGate.act_pauliMulIndex` for `cnot`. -/
theorem cnotCtrlPauli_pauliMul (a b a' b' : Fin 4) :
    cnotCtrlPauli (pauliMul a a') (pauliMul b b')
      = pauliMul (cnotCtrlPauli a b) (cnotCtrlPauli a' b') := by decide +revert

/-- The CNOT **target** tableau is multiplicative in both arguments simultaneously:
`tgt (a ⊙ a') (b ⊙ b') = tgt a b ⊙ tgt a' b'`. A `256`-case check. -/
theorem cnotTgtPauli_pauliMul (a b a' b' : Fin 4) :
    cnotTgtPauli (pauliMul a a') (pauliMul b b')
      = pauliMul (cnotTgtPauli a b) (cnotTgtPauli a' b') := by decide +revert

/-- **CNOT conjugation is multiplicative on Pauli indices**:
`cnotPauliString (g ⊙ h) c t = cnotPauliString g c t ⊙ cnotPauliString h c t`. Wire by wire this is
`cnotCtrlPauli_pauliMul` on the control, `cnotTgtPauli_pauliMul` on the target, and nothing off
them. No hypothesis `c ≠ t` is needed: both sides read the same wire in the degenerate case. -/
theorem cnotPauliString_pauliMulIndex (g h : Fin n → Fin 4) (c t : Fin n) :
    cnotPauliString (pauliMulIndex g h) c t
      = pauliMulIndex (cnotPauliString g c t) (cnotPauliString h c t) := by
  funext k
  rcases eq_or_ne k c with rfl | hkc
  · simpa [pauliMulIndex] using cnotCtrlPauli_pauliMul (g k) (g t) (h k) (h t)
  · rcases eq_or_ne k t with rfl | hkt
    · simp only [cnotPauliString, Function.update_of_ne hkc, Function.update_self, pauliMulIndex]
      exact cnotTgtPauli_pauliMul (g c) (g k) (h c) (h k)
    · simp only [cnotPauliString_of_ne _ c t hkc hkt, pauliMulIndex]

/-- **An elementary Clifford gate acts multiplicatively on Pauli indices**:
`γ.act (g ⊙ h) = γ.act g ⊙ γ.act h`. Since `checkRow` turns `⊙` into `+`, this is precisely the
statement that a Clifford gate acts *linearly* on check-matrix rows. Case check on the three
generators, using the multiplicative tableaux `hadamardPauli_pauliMul`, `phasePauli_pauliMul` and
`cnotPauliString_pauliMulIndex`. -/
theorem CliffordGate.act_pauliMulIndex (γ : CliffordGate n) (g h : Fin n → Fin 4) :
    γ.act (pauliMulIndex g h) = pauliMulIndex (γ.act g) (γ.act h) := by
  cases γ with
  | had j =>
      funext k
      rcases eq_or_ne k j with rfl | hkj
      · simpa [CliffordGate.act, pauliMulIndex] using hadamardPauli_pauliMul (g k) (h k)
      · simp [CliffordGate.act, Function.update_of_ne hkj, pauliMulIndex]
  | phase j =>
      funext k
      rcases eq_or_ne k j with rfl | hkj
      · simpa [CliffordGate.act, pauliMulIndex] using phasePauli_pauliMul (g k) (h k)
      · simp [CliffordGate.act, Function.update_of_ne hkj, pauliMulIndex]
  | cnot c t _ => exact cnotPauliString_pauliMulIndex g h c t

/-- **A Clifford circuit acts multiplicatively on Pauli indices**:
`U.act (g ⊙ h) = U.act g ⊙ U.act h`. By induction along the gate list from
`CliffordGate.act_pauliMulIndex`. Read through `checkVec` (which sends `⊙` to `+`) this is the
linearity of the Clifford action on `𝔽₂^{2n}` labels — the content packaged as
`cliffordLabelMap`. -/
theorem CliffordCircuit.act_pauliMulIndex (U : CliffordCircuit n) (g h : Fin n → Fin 4) :
    U.act (pauliMulIndex g h) = pauliMulIndex (U.act g) (U.act h) := by
  induction U with
  | nil => rfl
  | cons γ U ih => simp only [CliffordCircuit.act, ih, γ.act_pauliMulIndex]

/-! ### The `𝔽₂`-linear label action of a Clifford circuit -/

/-- The label action of a Clifford circuit is **additive**. Transporting `act` along the label
bijection: adding labels multiplies Paulis (`vecPauli_add`), the action is multiplicative
(`CliffordCircuit.act_pauliMulIndex`), and multiplying Paulis adds labels
(`checkVec_pauliMulIndex`). -/
private theorem checkVec_act_vecPauli_add (U : CliffordCircuit n)
    (u v : Fin n ⊕ Fin n → ZMod 2) :
    checkVec (U.act (vecPauli (u + v)))
      = checkVec (U.act (vecPauli u)) + checkVec (U.act (vecPauli v)) := by
  rw [vecPauli_add, U.act_pauliMulIndex, checkVec_pauliMulIndex]

/-- **The `𝔽₂`-linear label action of a Clifford circuit** `U`: the endomorphism of `𝔽₂^{2n}`
sending a label `v` to the label of the conjugated Pauli string, `checkVec (U.act (vecPauli v))`.
Additivity is `checkVec_act_vecPauli_add`; a `ZMod n`-module structure is unique on an additive
group, so every additive map is automatically `ZMod 2`-linear — that is
`AddMonoidHom.toZModLinearMap`, which also supplies `map_zero`. Its defining property on labels of
Pauli strings is `cliffordLabelMap_checkVec`, and its matrix — in the row-vector convention — is
`cliffordSymplectic`. -/
def cliffordLabelMap (U : CliffordCircuit n) :
    (Fin n ⊕ Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2) :=
  (AddMonoidHom.mk' (fun v => checkVec (U.act (vecPauli v)))
    (checkVec_act_vecPauli_add U)).toZModLinearMap 2

@[simp]
theorem cliffordLabelMap_apply (U : CliffordCircuit n) (v : Fin n ⊕ Fin n → ZMod 2) :
    cliffordLabelMap U v = checkVec (U.act (vecPauli v)) := rfl

/-- **The defining property of the label action**: on the label of a Pauli string `g` it returns the
label of the conjugated string, `cliffordLabelMap U (checkVec g) = checkVec (U.act g)`. -/
theorem cliffordLabelMap_checkVec (U : CliffordCircuit n) (g : Fin n → Fin 4) :
    cliffordLabelMap U (checkVec g) = checkVec (U.act g) := by
  rw [cliffordLabelMap_apply, vecPauli_checkVec]

/-! ### The symplectic matrix of a Clifford circuit -/

/-- **The symplectic matrix of a Clifford circuit** `U`: the `2n × 2n` matrix over `𝔽₂` through
which `U` acts on Pauli labels, in the row-vector convention `label ↦ label ᵥ* cliffordSymplectic U`
(`checkVec_act`). It is the matrix of the linear label action `cliffordLabelMap U`, transposed:
Mathlib's `LinearMap.toMatrix'` encodes the column action `mulVec`, and the transpose converts it to
the row action `vecMul` used for `(x | z)` labels throughout (Convention c2 of *Beyond
transversality*; `vecMul_fromBlocks_blocks`). It lies in the binary symplectic group
(`cliffordSymplectic_mem_binarySymplecticGroup`). -/
def cliffordSymplectic (U : CliffordCircuit n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  (LinearMap.toMatrix' (cliffordLabelMap U))ᵀ

/-- **The row action of the symplectic matrix is the label action**:
`v ᵥ* cliffordSymplectic U = cliffordLabelMap U v` for every label `v`. -/
theorem vecMul_cliffordSymplectic (U : CliffordCircuit n) (v : Fin n ⊕ Fin n → ZMod 2) :
    v ᵥ* cliffordSymplectic U = cliffordLabelMap U v := by
  rw [cliffordSymplectic, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
    LinearMap.toMatrix'_mulVec]

/-- **A Clifford circuit's label map is determined by its per-wire `pauliBit` action**: if the
image of the Pauli string `vecPauli (x | z)` has check bits `(x' k, z' k)` on every wire `k`, then
`cliffordLabelMap U (x | z) = (x' | z')`. The `pauliBit`-level companion of
`cliffordSymplectic_eq_of_labelMap` — the two together take a gate's per-wire tableau all the way to
its symplectic matrix. It packages the `funext`/`Sum` split shared by every `cliffordLabelMap_…`
generator lemma (`cliffordLabelMap_phase` and the elementary-gate images in
`CliffordSymplecticGeneration.lean`): the `inl`/`inr` coordinates read off the two components of the
per-wire pair (`checkVec_inl` / `checkVec_inr`). -/
theorem cliffordLabelMap_eq_of_pauliBit {U : CliffordCircuit n} {x z x' z' : Fin n → ZMod 2}
    (h : ∀ k, pauliBit (U.act (vecPauli (Sum.elim x z)) k) = (x' k, z' k)) :
    cliffordLabelMap U (Sum.elim x z) = Sum.elim x' z' := by
  funext i
  cases i with
  | inl k => simpa [CliffordCircuit.act] using congrArg Prod.fst (h k)
  | inr k => simpa [CliffordCircuit.act] using congrArg Prod.snd (h k)

/-- **A Clifford circuit's symplectic matrix is determined by its label action**: if
`cliffordLabelMap U v = v ᵥ* M` for every label `v`, then `cliffordSymplectic U = M`. The canonical
bridge for identifying a gate's symplectic image with an explicit matrix — one computes the label
action (a `cliffordLabelMap_…` lemma) and reads off the matrix through injectivity of the right row
action. Used by `cliffordSymplectic_phase` and by every elementary-gate image in
`CliffordSymplecticGeneration.lean`. -/
theorem cliffordSymplectic_eq_of_labelMap {U : CliffordCircuit n}
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)}
    (h : ∀ v, cliffordLabelMap U v = v ᵥ* M) : cliffordSymplectic U = M :=
  Matrix.vecMul_injective <| funext fun v => (vecMul_cliffordSymplectic U v).trans (h v)

/-- **The bridge, in the form used downstream**: conjugating a Pauli string by a Clifford circuit
acts on its `(x | z)` label by the matrix `cliffordSymplectic U`, acting on the right,
`checkVec (U.act g) = checkVec g ᵥ* cliffordSymplectic U`. -/
theorem checkVec_act (U : CliffordCircuit n) (g : Fin n → Fin 4) :
    checkVec (U.act g) = checkVec g ᵥ* cliffordSymplectic U := by
  rw [vecMul_cliffordSymplectic, cliffordLabelMap_checkVec]


/-! ### Functoriality -/

/-- The empty circuit acts trivially on labels: `cliffordLabelMap [] = id`. -/
theorem cliffordLabelMap_nil : cliffordLabelMap ([] : CliffordCircuit n) = LinearMap.id := by
  ext v i
  simp [CliffordCircuit.act]

/-- **The empty circuit has the identity symplectic matrix**: `cliffordSymplectic [] = 1`. -/
@[simp]
theorem cliffordSymplectic_nil : cliffordSymplectic ([] : CliffordCircuit n) = 1 := by
  rw [cliffordSymplectic, cliffordLabelMap_nil, LinearMap.toMatrix'_id, Matrix.transpose_one]

/-- The label action of a composed circuit is the composed label action:
`cliffordLabelMap (U ++ V) = cliffordLabelMap U ∘ₗ cliffordLabelMap V` (in `U ++ V` the sub-circuit
`V` acts first, `CliffordCircuit.act_append`). -/
theorem cliffordLabelMap_append (U V : CliffordCircuit n) :
    cliffordLabelMap (U ++ V) = (cliffordLabelMap U).comp (cliffordLabelMap V) := by
  ext v i
  simp [CliffordCircuit.act_append]

/-- **Functoriality of the symplectic matrix**:
`cliffordSymplectic (U ++ V) = cliffordSymplectic V * cliffordSymplectic U`. The order is reversed
because labels are *row* vectors acted on from the right, while in `U ++ V` the circuit `V` acts
first: `w ᵥ* (S_V * S_U) = (w ᵥ* S_V) ᵥ* S_U`. Together with `cliffordSymplectic_nil` this says
`cliffordSymplectic` is a monoid anti-homomorphism from Clifford circuits under concatenation into
`Sp(2n, 𝔽₂)`. -/
theorem cliffordSymplectic_append (U V : CliffordCircuit n) :
    cliffordSymplectic (U ++ V) = cliffordSymplectic V * cliffordSymplectic U := by
  rw [cliffordSymplectic, cliffordLabelMap_append, LinearMap.toMatrix'_comp, Matrix.transpose_mul]
  rfl

/-! ### The matrix is symplectic -/

/-- Two natural numbers with the same parity have the same image in `ZMod 2`. The arithmetic step
turning the parity statement `CliffordCircuit.act_pauliAnticommCount_even_iff` into an equality of
symplectic pairings. -/
private theorem natCast_zmod2_eq_of_even_iff {m m' : ℕ} (h : Even m ↔ Even m') :
    (m : ZMod 2) = (m' : ZMod 2) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.even_iff, Nat.even_iff] at *
  omega

/-- **The Clifford label action preserves the symplectic form**:
`⟨r(U.act g), r(U.act h)⟩ = ⟨r(g), r(h)⟩` for the twisted inner product `x Λ yᵀ` of N&C
eq. (10.84). This is the physical content that makes the action symplectic: the form computes
commutation (Exercise 10.33, `symplecticForm_checkVec`), and conjugation by a unitary preserves
commutation (`CliffordCircuit.act_pauliAnticommCount_even_iff`). -/
theorem symplecticForm_checkVec_act (U : CliffordCircuit n) (g h : Fin n → Fin 4) :
    symplecticForm (checkVec (U.act g)) (checkVec (U.act h))
      = symplecticForm (checkVec g) (checkVec h) := by
  rw [symplecticForm_checkVec, symplecticForm_checkVec]
  exact natCast_zmod2_eq_of_even_iff (U.act_pauliAnticommCount_even_iff g h)

/-- The symplectic matrix preserves the form on **all** of `𝔽₂^{2n}`, not just on labels of a
distinguished family: `⟨u ᵥ* S, v ᵥ* S⟩ = ⟨u, v⟩`. Every label is the check vector of a Pauli string
(`checkVec_vecPauli`), so this is `symplecticForm_checkVec_act` transported along the bijection. -/
theorem symplecticForm_vecMul_cliffordSymplectic (U : CliffordCircuit n)
    (u v : Fin n ⊕ Fin n → ZMod 2) :
    symplecticForm (u ᵥ* cliffordSymplectic U) (v ᵥ* cliffordSymplectic U)
      = symplecticForm u v := by
  obtain ⟨p, rfl⟩ := checkVecEquiv.surjective u
  obtain ⟨q, rfl⟩ := checkVecEquiv.surjective v
  simp only [checkVecEquiv_apply]
  rw [← checkVec_act, ← checkVec_act]
  exact symplecticForm_checkVec_act U p q

/-- **The headline: a Clifford circuit acts on Pauli labels by a binary symplectic matrix.**
`cliffordSymplectic U ∈ Sp(2n, 𝔽₂)` — the matrix through which a Clifford circuit transforms the
`(x | z)` labels of Pauli strings (`checkVec_act`) preserves the symplectic form of
Nielsen & Chuang eq. (10.84), i.e. satisfies `S Λ Sᵀ = Λ`
(`mem_binarySymplecticGroup_iff`).

This is Gottesman's classical fact: conjugation by a Clifford unitary is a *symplectic* linear map
on Pauli labels. The reason is commutation — two Pauli strings commute iff their labels pair
trivially under `Λ` (Exercise 10.33), and conjugation by a unitary cannot change whether two
operators commute — which is exactly `symplecticForm_vecMul_cliffordSymplectic`. The passage from
"preserves the form" to "`S Λ Sᵀ = Λ`" is the general form-side membership criterion
`mem_binarySymplecticGroup_iff_symplecticForm_vecMul`. -/
theorem cliffordSymplectic_mem_binarySymplecticGroup (U : CliffordCircuit n) :
    cliffordSymplectic U ∈ binarySymplecticGroup (Fin n) :=
  mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mpr
    (symplecticForm_vecMul_cliffordSymplectic U)

/-! ### A worked generator: the phase gate is a `Z`-shear -/


end CliffordCSS

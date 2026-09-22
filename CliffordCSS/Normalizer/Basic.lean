import CliffordCSS.Pauli.CliffordCircuit
import CliffordCSS.Pauli.Group

/-!
# The Pauli normalizer, and uniqueness up to global phase (Theorem 10.6, part 1)

This file is pure mathematics : it opens the formalisation of
Nielsen & Chuang **Theorem 10.6** — *any unitary `U` on `n` qubits with `U Gₙ U† ⊆ Gₙ` is, up to a
global phase, a product of `O(n²)` Hadamard/phase/CNOT gates*. It supplies the **framework** (the
matrix-level normalizer predicate), the **easy direction** (every Clifford circuit is a Pauli
normalizer), and the **reduction that gives the theorem its "up to a global phase" shape**: two
unitaries with the *same conjugation action* on the Pauli group agree up to a unit scalar. Every
statement names only raw matrix / index data (`Matrix`, `CliffordCSS.pauliString`,
`CliffordCSS.PauliGroup`, `Matrix.unitaryGroup`, `Fin n → Fin 4`).

## What is proved

* `exists_smul_one_of_commute_pauliString` — **the Pauli commutant is the scalars.** A matrix `W`
  commuting with every Pauli string `P_g` is a scalar `c • 1`. This is *Schur's lemma for the Pauli
  group*: since the `4ⁿ` Pauli strings are a basis of the `2ⁿ×2ⁿ` matrices (`pauliBasis`), `W`
  commutes with every matrix, hence lies in the centre of the matrix ring, which is the scalars
  (`Matrix.center_eq_scalar_image`). It is the linear-algebraic engine of the whole reduction.

* `IsPauliNormalizer U` — **the normalizer predicate.** `U` is unitary and conjugates every element
  of the Pauli group `Gₙ` (via its faithful representation `PauliGroup.toMat`) back into `Gₙ`. This
  is exactly N&C's hypothesis "if `g ∈ Gₙ` then `U g U† ∈ Gₙ`", i.e. membership in the normalizer
  `N(Gₙ)`.

* `unitary_eq_smul_of_conj_pauliString_eq` — **uniqueness up to global phase (the reduction).** If
  two unitaries `U, V` conjugate every Pauli string identically (`U P_g U† = V P_g V†` for all `g`),
  then `U = c • V` for a unit scalar `c` (`‖c‖ = 1`). Hence a normalizer unitary is determined, up
  to a global phase, by its conjugation action on `Gₙ` — the precise sense of Theorem 10.6's "up to
  a global phase", and what reduces the theorem to realising that action by a Clifford circuit.

* `unitary_isGlobalPhase_of_conj_pauliString_eq_self` — **Nielsen & Chuang Exercise 10.38 (core).**
  A unitary that fixes every Pauli string under conjugation (`U P_g U† = P_g`) is a global phase
  `c • 1`, `‖c‖ = 1`. The `V = 1` special case of the reduction; the physical statement that only
  scalars commute with the whole Pauli group.

* `CliffordCircuit.sign_eq_one_or_neg_one` / `cliffordCircuit_isPauliNormalizer` — **the easy
  direction of Theorem 10.6.** The conjugation phase of a Clifford circuit is `±1`, and therefore
  every Clifford circuit is a Pauli normalizer: `U P_a U† = ±P_{U.act a}`, so `U (iˢ P_a) U† =
  i^{s'} P_{U.act a} ∈ Gₙ` (`CliffordCircuit.conj_pauliString`). This is the containment
  `⟨H, S, CNOT⟩ ⊆ N(Gₙ)`; Theorem 10.6 is the converse.

* `IsPauliNormalizer.exists_sign_conj_pauliString` — **the sign is `±1`.** A normalizer conjugates
  each phase-free Pauli string to a `±1` multiple of a Pauli string, `U P_a U† = z • P_b` with
  `z ∈ {1, -1}`. The phase is real because `P_a` is an involution, so `(U P_a U†)² = 1` forces
  `z² = 1`; this is the shape (signs `±1`, never `±i`) the synthesis of Exercise 10.40 uses.

* `IsPauliNormalizer.exists_signedPerm` — **a normalizer is a `±1`-signed permutation of the Pauli
  strings.** Bundles the per-string data into a permutation `σ : Equiv.Perm (Fin n → Fin 4)` and a
  sign function `ε` valued in `{1, -1}` with `U P_a U† = ε a • P_{σ a}`. Injectivity of the action
  (hence bijectivity, on the finite index set) comes from conjugating back by `U` and
  Hilbert–Schmidt orthogonality. It is the combinatorial object Exercise 10.40 synthesises.

* `unitary_eq_smul_cliffordCircuit_of_conj_eq` — **the converse reduces to synthesis.** If a unitary
  conjugates the Pauli strings exactly as a Clifford circuit `C` does, it equals `C` up to a global
  phase. With `exists_signedPerm` this reduces the converse of Theorem 10.6 to a combinatorial
  problem: synthesise a Clifford circuit realising the normalizer's signed permutation.

* `unitaryConj_commute_iff` / `IsPauliNormalizer.exists_signedPerm_symplectic` — **a normalizer's
  signed permutation is symplectic.** Conjugation by a unitary preserves commutation (it is an
  algebra automorphism), so a normalizer's induced permutation `σ` of the Pauli-string indices
  preserves the binary symplectic form (`pauliAnticommCount`, mod 2) of Exercise 10.33 — in
  particular it maps anticommuting Pauli strings to anticommuting ones. This is the structural
  invariant the multi-qubit inductive synthesis of Exercise 10.40 (parts 2–3) rests on (N&C part 2
  opens by noting the images of the anticommuting `Z₁, X₁` anticommute).

## Design notes

* The reduction is stated over `pauliString` (the phase-free Pauli operators) because that is where
  `pauliBasis`/`CliffordCircuit.conj_pauliString` live; the normalizer *predicate* is stated over
  the full group `PauliGroup.toMat = iˢ • P_a` (phases included) to be faithful to N&C's `Gₙ`. The
  two match because conjugation is `ℂ`-linear, so acting on `iˢ P_a` is acting on `P_a` scaled.
* `unitary_eq_smul_of_conj_pauliString_eq` needs no normalizer hypothesis: it holds for *any* two
  unitaries with equal conjugation action. The normalizer only enters when one shows the action is
  realised by a Clifford circuit (the converse, developed in later PRs — the inductive synthesis of
  N&C Exercise 10.40 and its `O(n²)` gate count).
-/

open Matrix

noncomputable section

namespace CliffordCSS

variable {n : ℕ}

/-! ### Schur's lemma for the Pauli group: the commutant is the scalars -/


/-! ### The normalizer predicate -/


/-! ### Uniqueness up to global phase (the reduction) -/


/-! ### The easy direction: every Clifford circuit is a Pauli normalizer -/

/-- The single-gate Hadamard conjugation phase is `±1`: `hadamardPauliSign a ∈ {1, -1}`. -/
private theorem hadamardPauliSign_eq_one_or_neg_one (a : Fin 4) :
    hadamardPauliSign a = 1 ∨ hadamardPauliSign a = -1 := by
  fin_cases a <;> simp [hadamardPauliSign]

/-- The single-gate phase-gate conjugation phase is `±1`: `phasePauliSign a ∈ {1, -1}`. -/
private theorem phasePauliSign_eq_one_or_neg_one (a : Fin 4) :
    phasePauliSign a = 1 ∨ phasePauliSign a = -1 := by
  fin_cases a <;> simp [phasePauliSign]

/-- The single-gate CNOT conjugation phase is `±1`: `cnotPauliSign a b ∈ {1, -1}`. -/
private theorem cnotPauliSign_eq_one_or_neg_one (a b : Fin 4) :
    cnotPauliSign a b = 1 ∨ cnotPauliSign a b = -1 := by
  fin_cases a <;> fin_cases b <;> simp [cnotPauliSign]

/-- An elementary Clifford gate conjugates a Pauli string with a `±1` phase. -/
theorem CliffordGate.sign_eq_one_or_neg_one (γ : CliffordGate n) (g : Fin n → Fin 4) :
    γ.sign g = 1 ∨ γ.sign g = -1 := by
  cases γ with
  | had j => simpa [CliffordGate.sign] using hadamardPauliSign_eq_one_or_neg_one (g j)
  | phase j => simpa [CliffordGate.sign] using phasePauliSign_eq_one_or_neg_one (g j)
  | cnot c t _ => simpa [CliffordGate.sign] using cnotPauliSign_eq_one_or_neg_one (g c) (g t)

/-- **A Clifford circuit conjugates a Pauli string with a `±1` phase**: `U.sign g ∈ {1, -1}`, since
it is a product of the per-gate `±1` phases (`CliffordGate.sign_eq_one_or_neg_one`). -/
theorem CliffordCircuit.sign_eq_one_or_neg_one (U : CliffordCircuit n) (g : Fin n → Fin 4) :
    CliffordCircuit.sign U g = 1 ∨ CliffordCircuit.sign U g = -1 := by
  induction U with
  | nil => left; rfl
  | cons γ U ih =>
      rw [CliffordCircuit.sign]
      rcases ih with hU | hU <;>
        rcases γ.sign_eq_one_or_neg_one (CliffordCircuit.act U g) with hγ | hγ <;>
        simp [hU, hγ]

/-- The Clifford-circuit conjugation phase is a fourth root of unity: `U.sign g = iᵏ` for some
`k : ZMod 4` (indeed `k ∈ {0, 2}`, i.e. `±1`). Packaging `sign_eq_one_or_neg_one` in the phase
form `zmod4Pow` needed to land the conjugate back in the Pauli group `Gₙ`. -/
theorem CliffordCircuit.sign_eq_zmod4Pow (U : CliffordCircuit n) (g : Fin n → Fin 4) :
    ∃ k : ZMod 4, CliffordCircuit.sign U g = zmod4Pow k := by
  rcases CliffordCircuit.sign_eq_one_or_neg_one U g with h | h
  · exact ⟨0, by rw [h, zmod4Pow_zero]⟩
  · exact ⟨2, by rw [h, zmod4Pow_two]⟩


/-! ### The induced signed permutation of a normalizer, and the reduction to Clifford synthesis -/


/-! ### Multiplicativity of conjugation by an isometry -/


/-! ### Single-qubit case: `X` and `Z` determine the conjugation action (Exercise 10.40 part 1) -/


/-! ### Single-qubit synthesis: `H`/`S` generate the normalizer up to phase (Exercise 10.40 part 1)

The base case of the converse of Theorem 10.6. A single-qubit normalizer `U` induces a `±1`-signed
permutation of the four Pauli-string indices `{I, X, Y, Z}` (`exists_signedPerm`); it fixes `I`, so
it sends `X` and `Z` to a *distinct* pair of non-identity strings with `±1` signs. By the
`X, Z`-determinacy reduction `unitary_eq_smul_of_conj_singleQubit_XZ` it suffices to realise those
two images by a Clifford circuit — and the single-qubit `H`, `S` gates already do: their phase-free
action is a transposition of the index set (`H : X ↔ Z`, `S : X ↔ Y`), so their words realise every
permutation of `{X, Y, Z}` (`⟨(X Z), (X Y)⟩ = S₃`, `exists_cliffordCircuit_singleQubit_act`), and
the trivial-action Pauli-conjugation words (`Z = S²`, `X = H S² H`, `Y = X · Z`) realise every
`±1` sign pattern on `X, Z` (`exists_cliffordCircuit_singleQubit_signFix`). Gluing a permutation
word to a sign-fix word (`act_append` / `sign_append`) hits an arbitrary valid `(X, Z)` image, and
the determinacy reduction upgrades that to `U = c • C.toMatrix` for an `H`/`S`-word `C`, `‖c‖ = 1`
— Theorem 10.6 for `n = 1`. (The `n + 1` inductive step and the `O(n²)` gate count are the deferred
remaining parts of Exercise 10.40.) -/


/-! ### A normalizer preserves the commutation (symplectic) structure of the Pauli strings

The structural invariant driving the multi-qubit inductive synthesis (Nielsen & Chuang Exercise
10.40 parts 2–3): conjugation by a unitary is a `*`-algebra automorphism, hence preserves
commutation and anticommutation. A Pauli normalizer therefore acts on the Pauli strings by a
transformation that respects the **binary symplectic form** (`pauliAnticommCount`, mod 2) of
Exercise 10.33 — its induced `±1`-signed permutation `σ` of the Pauli-string indices is a
*symplectic* permutation. In particular it sends anticommuting Pauli strings to anticommuting ones,
which is precisely how Nielsen & Chuang open part 2: "since `Z₁` and `X₁` anticommute, `U Z₁ U†` and
`U X₁ U†` anticommute". -/

/-- **Conjugation by a unitary preserves commutation.** For a unitary `U` and any matrices `P, Q`,
the conjugates `U P U†` and `U Q U†` commute iff `P` and `Q` do. Conjugation `M ↦ U M U†` is the
`*`-algebra automorphism `Unitary.conjStarAlgAut ℂ _ ⟨U, hU⟩` (a `StarAlgEquiv`, so a bijective
ring homomorphism), and commutation is transported along any multiplicative map both ways
(`Commute.map`, using the inverse `f.symm` for the reverse direction). This is the algebraic reason
a Pauli normalizer preserves the commutation structure of `Gₙ`. -/
theorem unitaryConj_commute_iff {N : Type*} [Fintype N] [DecidableEq N]
    {U : Matrix N N ℂ} (hU : U ∈ Matrix.unitaryGroup N ℂ) (P Q : Matrix N N ℂ) :
    Commute (U * P * Uᴴ) (U * Q * Uᴴ) ↔ Commute P Q := by
  set f := Unitary.conjStarAlgAut ℂ (Matrix N N ℂ) ⟨U, hU⟩ with hf_def
  have hf : ∀ M : Matrix N N ℂ, f M = U * M * Uᴴ := fun M => by
    rw [hf_def, Unitary.conjStarAlgAut_apply]
    simp only [star_eq_conjTranspose, Matrix.mul_assoc]
  rw [← hf P, ← hf Q]
  exact ⟨fun h => by simpa using h.map (f.symm : _ ≃⋆ₐ[ℂ] _), fun h => h.map f⟩


end CliffordCSS

end

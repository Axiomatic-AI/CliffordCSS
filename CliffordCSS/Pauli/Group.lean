import CliffordCSS.Symplectic.CheckMatrix

/-!
# The `n`-qubit Pauli group and its faithful check-row representation

This file is pure mathematics : it builds the **`n`-qubit Pauli
group** `Gₙ` (Nielsen & Chuang §10.5, the group whose elements are the `n`-fold tensor products of
`{I, X, Y, Z}` together with an overall multiplicative factor `±1, ±i`) as an honest group, and the
**total check-row homomorphism** `r : Gₙ → 𝔽₂^{2n}` that N&C uses in the proof of Proposition 10.3.
Everything here names only raw matrix / index data (`Matrix`, `CliffordCSS.pauliString`,
`CliffordCSS.checkRow`, `ZMod`, `Fin n → Fin 4`).

## The group

An element of `Gₙ` is `iˢ · P_a`, a Pauli string `P_a` (`a : Fin n → Fin 4`) scaled by a
fourth-root-of-unity phase `iˢ` (`s : ZMod 4`). We model this **abstractly** by the data pair

`PauliGroup n := { phase : ZMod 4, idx : Fin n → Fin 4 }`,

With the twisted product `(s, a) · (t, b) = (s + t + phasePow a b, a ⊙ b)`, where `a ⊙ b`
(`pauliMulIndex`) is the componentwise Pauli-index product and `phasePow a b : ZMod 4` collects the
per-qubit product phases (`pauliMulPhase`) written as powers of `i`. This is the abstract structure
of `Gₙ`; it is identified with the actual operators by the **faithful representation**

`pauliRep : PauliGroup n →* Matrix …, (s, a) ↦ iˢ • P_a`,

An **injective** monoid homomorphism (`pauliRep_injective`). Modelling the group abstractly (rather
than as a `Subgroup` of matrix units) makes the check-row map the trivial second-projection map
below; faithfulness is recorded once, by the injective representation.

The `Group` instance is derived *through* the representation: since `pauliRep` is injective and
multiplicative and lands in the (associative) matrix ring, the group axioms for `PauliGroup n`
reduce to matrix identities (associativity from `mul_assoc`, the inverse law from the involution
`pauliString_mul_self`). No group-cocycle case check is needed.

## The check-row homomorphism

The check row of a Pauli-group element is the check row of its index — the phase is discarded, as in
N&C ("the check matrix doesn't contain any information about the multiplicative factors"):

`checkRowHom (s, a) := checkRow a`.

It is a homomorphism `(Gₙ, ·) → (𝔽₂^{2n}, +)` — `checkRowHom (p q) = checkRowHom p + checkRowHom q`
(`checkRowHom_mul`, from `checkRow_pauliMulIndex`) — with *bare* kernel `checkRowHom p = 0 ↔
p.idx = 0` (`checkRowHom_eq_zero_iff`, from `checkRow_eq_zero_iff`): the row vanishes exactly on the
phase-only elements `iˢ · I`. This is the "addition in the row representation corresponds to
multiplication of group elements" of the Proposition 10.3 proof, now for the *full* group (phases
included), not just the phase-free strings of `CliffordCSS/Symplectic/CheckMatrix.lean`.

The element `negOne : PauliGroup n := (2, 0)` represents `-I` (`pauliRep_negOne`); the hypothesis
`-I ∉ S` of Proposition 10.3 is `negOne ∉ S`. Turning the bare kernel into a *trivial* kernel on a
subgroup `S` with `negOne ∉ S` (Ex 10.34/10.35) is the next step, developed downstream.

## Design notes

* The phase group is `ZMod 4` with `iˢ` realised by `zmod4Pow s = Iˢ·ᵛᵃˡ`, a monoid homomorphism
  from `(ZMod 4, +)` to `(ℂ, ·)` (`zmod4Pow_add`, using `I⁴ = 1`), injective and nonzero on the four
  values `1, i, -1, -i`. The `n`-qubit phase exponent `phasePow a b = ∑ₖ singlePhasePow (aₖ) (bₖ)`
  sums the single-qubit `i`-power table `singlePhasePow`, chosen so that `zmod4Pow (singlePhasePow
  a b) = pauliMulPhase a b`; hence `zmod4Pow (phasePow a b) = ∏ₖ pauliMulPhase (aₖ) (bₖ)`, exactly
  the scalar in the Pauli-string product law `pauliString_mul_eq_smul` — this is what makes
  `pauliRep` multiplicative.
* Injectivity of `pauliRep` comes from the Hilbert–Schmidt orthogonality of the Pauli strings:
  pairing `iˢ • P_a = iᵗ • P_b` against `P_a` and `P_b` under the trace (`pauliString_trace_mul`)
  forces `a = b` (else a nonzero scalar would vanish) and then `iˢ = iᵗ`, hence `s = t`.
-/

open Matrix Complex

open scoped BigOperators

namespace CliffordCSS

/-! ### The fourth-root-of-unity phase `iˢ` -/

/-- The **fourth-root-of-unity phase** `iˢ` for `s : ZMod 4`, defined as `Complex.I ^ s.val`. Since
`I⁴ = 1`, this descends from `ℤ`/`ℕ` to `ZMod 4` and is a homomorphism `(ZMod 4, +) → (ℂ, ·)`
(`zmod4Pow_add`), taking the four values `1, i, -1, -i`. It supplies the `±1, ±i` overall factor of
a Pauli-group element. -/
noncomputable def zmod4Pow (s : ZMod 4) : ℂ := Complex.I ^ s.val

@[simp] theorem zmod4Pow_zero : zmod4Pow 0 = 1 := by rw [zmod4Pow]; norm_num

@[simp] theorem zmod4Pow_one : zmod4Pow 1 = Complex.I := by
  rw [zmod4Pow, show (1 : ZMod 4).val = 1 from rfl, pow_one]

@[simp] theorem zmod4Pow_two : zmod4Pow 2 = -1 := by
  rw [zmod4Pow, show (2 : ZMod 4).val = 2 from rfl]; norm_num [pow_succ, Complex.I_mul_I]

@[simp] theorem zmod4Pow_three : zmod4Pow 3 = -Complex.I := by
  rw [zmod4Pow, show (3 : ZMod 4).val = 3 from rfl]; norm_num [pow_succ, Complex.I_mul_I]

/-- `iˢ ≠ 0`: a power of the nonzero number `i` is nonzero. -/
theorem zmod4Pow_ne_zero (s : ZMod 4) : zmod4Pow s ≠ 0 := by
  rw [zmod4Pow]; exact pow_ne_zero _ Complex.I_ne_zero

/-- **The phase is a homomorphism** `(ZMod 4, +) → (ℂ, ·)`: `i^(x+y) = iˣ · iʸ`. Because `I⁴ = 1`,
the power `Iᵏ` depends only on `k mod 4`, and `(x + y).val ≡ x.val + y.val (mod 4)`
(`ZMod.val_add`). -/
theorem zmod4Pow_add (x y : ZMod 4) : zmod4Pow (x + y) = zmod4Pow x * zmod4Pow y := by
  have hI4 : ∀ a : ℕ, Complex.I ^ (a % 4) = Complex.I ^ a := by
    intro a
    conv_rhs => rw [← Nat.div_add_mod a 4, pow_add, pow_mul]
    norm_num [pow_succ, Complex.I_mul_I]
  rw [zmod4Pow, zmod4Pow, zmod4Pow, ZMod.val_add, hI4, pow_add]

/-- The phase `iˢ` is **injective** in `s`: the four values `1, i, -1, -i` are distinct. -/
theorem zmod4Pow_injective : Function.Injective zmod4Pow := by
  intro x y h
  simp only [zmod4Pow] at h
  fin_cases x <;> fin_cases y <;> revert h <;>
    simp only [ZMod.val] <;> norm_num [Complex.ext_iff, pow_succ, Complex.I_mul_I]

/-- **The phase conjugates as its negation**: `zmod4Pow (-s) = star (zmod4Pow s)` (i.e.
`star (iˢ) = i⁻ˢ`). Both `zmod4Pow (-s)` and `star (zmod4Pow s)` are the inverse of the nonzero
unit-modulus number `zmod4Pow s` — `zmod4Pow s · zmod4Pow (-s) = 1` by `zmod4Pow_add`, and
`zmod4Pow s · star (zmod4Pow s) = 1` by a finite `ZMod 4` case check — so they agree by left
cancellation. This is what makes each `PauliGroup.toMat` unitary (`PauliGroup.toMat_inv`). -/
theorem zmod4Pow_neg (s : ZMod 4) : zmod4Pow (-s) = star (zmod4Pow s) := by
  have hz : zmod4Pow s ≠ 0 := zmod4Pow_ne_zero s
  have h1 : zmod4Pow s * zmod4Pow (-s) = 1 := by
    rw [← zmod4Pow_add, add_neg_cancel, zmod4Pow_zero]
  have h2 : zmod4Pow s * star (zmod4Pow s) = 1 := by
    fin_cases s <;>
      simp only [zmod4Pow, ZMod.val] <;>
      norm_num [Complex.ext_iff, pow_succ, Complex.I_mul_I, Complex.star_def]
  exact mul_left_cancel₀ hz (h1.trans h2.symm)


/-- The phase carries finite sums to finite products: `i^(∑ᵢ fᵢ) = ∏ᵢ i^(fᵢ)`. Finset induction on
`zmod4Pow_zero` and `zmod4Pow_add`. -/
theorem zmod4Pow_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 4) :
    zmod4Pow (∑ i ∈ s, f i) = ∏ i ∈ s, zmod4Pow (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zmod4Pow_add, ih]

/-! ### The Pauli-string product phase as an exponent of `i` -/

/-- The **single-qubit product-phase exponent** `singlePhasePow a b : ZMod 4`, the power `s` with
`iˢ = ζ(a, b)` (`pauliMulPhase`) in the single-qubit product `σ_a σ_b = ζ(a,b) σ_{a⊙b}`. Read off
`pauliMulPhase` (`1 = i⁰`, `i = i¹`, `-1 = i²`, `-i = i³`). -/
def singlePhasePow : Fin 4 → Fin 4 → ZMod 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 3], ![0, 3, 0, 1], ![0, 1, 3, 0]]

/-- `singlePhasePow` is the `i`-exponent of the single-qubit product phase: `i^(singlePhasePow a b)
= pauliMulPhase a b`. A finite `4 × 4` case check. -/
theorem zmod4Pow_singlePhasePow (a b : Fin 4) :
    zmod4Pow (singlePhasePow a b) = pauliMulPhase a b := by
  fin_cases a <;> fin_cases b <;> simp [singlePhasePow, pauliMulPhase]

/-- The **`n`-qubit product-phase exponent** `phasePow a b : ZMod 4`, the power `s` with `iˢ =
∏ₖ ζ(aₖ, bₖ)` the total phase in the Pauli-string product law. It is the sum of the per-qubit
exponents `∑ₖ singlePhasePow (aₖ) (bₖ)`. -/
def phasePow {n : ℕ} (a b : Fin n → Fin 4) : ZMod 4 := ∑ k, singlePhasePow (a k) (b k)

/-- `i^(phasePow a b) = ∏ₖ pauliMulPhase (aₖ) (bₖ)`: the phase exponent exponentiates to the total
scalar in the Pauli-string product law `pauliString_mul_eq_smul`. Combines `zmod4Pow_sum` with the
single-qubit `zmod4Pow_singlePhasePow`. -/
theorem zmod4Pow_phasePow {n : ℕ} (a b : Fin n → Fin 4) :
    zmod4Pow (phasePow a b) = ∏ k, pauliMulPhase (a k) (b k) := by
  rw [phasePow, zmod4Pow_sum]
  exact Finset.prod_congr rfl fun k _ => zmod4Pow_singlePhasePow (a k) (b k)

/-! ### The `n`-qubit Pauli group -/

/-- The **`n`-qubit Pauli group** `Gₙ` (Nielsen & Chuang §10.5), modelled abstractly by its data: a
fourth-root-of-unity phase `phase : ZMod 4` (the `iˢ` factor) and a Pauli-string index `idx : Fin n
→ Fin 4`. The element it represents is `iᵖʰᵃˢᵉ · P_idx` (`pauliRep`). -/
@[ext]
structure PauliGroup (n : ℕ) where
  /-- The fourth-root-of-unity phase power `s` (the overall factor `iˢ`). -/
  phase : ZMod 4
  /-- The Pauli-string index `a : Fin n → Fin 4` (one of `I, X, Y, Z` per qubit). -/
  idx : Fin n → Fin 4

namespace PauliGroup

variable {n : ℕ}

/-- Group multiplication `(s, a) · (t, b) = (s + t + phasePow a b, a ⊙ b)`: indices multiply
componentwise (`pauliMulIndex`) and the phases add, with the extra `phasePow a b` from the
Pauli-string product phase. -/
instance : Mul (PauliGroup n) :=
  ⟨fun p q => ⟨p.phase + q.phase + phasePow p.idx q.idx, pauliMulIndex p.idx q.idx⟩⟩

/-- The identity `(0, 0)`: phase `i⁰ = 1` and the all-identity index (`P₀ = I`). -/
instance : One (PauliGroup n) := ⟨⟨0, 0⟩⟩

/-- Inversion `(s, a)⁻¹ = (-s, a)`: a Pauli string is an involution, so only the phase inverts. -/
instance : Inv (PauliGroup n) := ⟨fun p => ⟨-p.phase, p.idx⟩⟩

@[simp] theorem mul_phase (p q : PauliGroup n) :
    (p * q).phase = p.phase + q.phase + phasePow p.idx q.idx := rfl

@[simp] theorem mul_idx (p q : PauliGroup n) : (p * q).idx = pauliMulIndex p.idx q.idx := rfl

@[simp] theorem one_phase : (1 : PauliGroup n).phase = 0 := rfl

@[simp] theorem one_idx : (1 : PauliGroup n).idx = 0 := rfl

@[simp] theorem inv_phase (p : PauliGroup n) : p⁻¹.phase = -p.phase := rfl

@[simp] theorem inv_idx (p : PauliGroup n) : p⁻¹.idx = p.idx := rfl

/-- The **faithful matrix representation** of a Pauli-group element: `(s, a) ↦ iˢ • P_a`, the
operator `iˢ · pauliString a`. This is the actual Pauli operator the abstract pair encodes; it is a
monoid homomorphism (`pauliRep`) and injective (`toMat_injective`). -/
noncomputable def toMat (p : PauliGroup n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  zmod4Pow p.phase • pauliString p.idx

/-- `toMat` is **multiplicative**: `toMat (p q) = toMat p · toMat q`. The phases combine via
`zmod4Pow_add` and `zmod4Pow_phasePow` into exactly the scalar of the Pauli-string product law
`pauliString_mul_eq_smul`. -/
theorem toMat_mul (p q : PauliGroup n) : toMat (p * q) = toMat p * toMat q := by
  simp only [toMat, mul_phase, mul_idx]
  rw [smul_mul_smul_comm, pauliString_mul_eq_smul, smul_smul, zmod4Pow_add, zmod4Pow_add,
    zmod4Pow_phasePow]

/-- `toMat` sends the identity to `1`: `i⁰ • P₀ = 1 • I = I`. -/
theorem toMat_one : toMat (1 : PauliGroup n) = 1 := by
  simp only [toMat, one_phase, one_idx, zmod4Pow_zero, one_smul, pauliString_eq_one_iff]

/-- The representation of a **phase-`+1`** element is just its Pauli string: `toMat ⟨0, a⟩ = P_a`
(`i⁰ • P_a = 1 • P_a`). The general form of the specific `xPauli_toMat`; the normal form for the
phase-free (Hermitian) lift of a Pauli string. -/
@[simp] theorem toMat_mk_zero (a : Fin n → Fin 4) :
    toMat (⟨0, a⟩ : PauliGroup n) = pauliString a := by
  simp only [toMat, zmod4Pow_zero, one_smul]

/-- **Faithfulness**: the representation `toMat` is injective — distinct abstract Pauli-group
elements give distinct operators. Pairing `iˢ • P_a = iᵗ • P_b` against `P_a` (resp. `P_b`) under
the trace and using the Hilbert–Schmidt orthogonality `pauliString_trace_mul` forces `a = b` (else a
nonzero scalar would vanish), and then `iˢ = iᵗ`, so `s = t` (`zmod4Pow_injective`). -/
theorem toMat_injective : Function.Injective (toMat (n := n)) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  simp only [toMat] at h
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have key : ∀ m, zmod4Pow s * (if m = a then (2 : ℂ) ^ n else 0)
      = zmod4Pow t * (if m = b then (2 : ℂ) ^ n else 0) := by
    intro m
    have hh := congrArg (fun M => (pauliString m * M).trace) h
    simpa only [Matrix.mul_smul, Matrix.trace_smul, pauliString_trace_mul, smul_eq_mul] using hh
  have hab : a = b := by
    by_contra hab
    have ea := key a
    rw [if_pos rfl, if_neg hab, mul_zero] at ea
    exact zmod4Pow_ne_zero s ((mul_eq_zero.mp ea).resolve_right h2)
  subst hab
  have ea := key a
  rw [if_pos rfl] at ea
  have hst : s = t := zmod4Pow_injective (mul_right_cancel₀ h2 ea)
  subst hst; rfl

/-- **The adjoint of a Pauli-group element is its inverse**: `toMat p⁻¹ = (toMat p)†`. Since
`toMat p = iˢ • P_a` with `P_a` Hermitian (`pauliString_isHermitian`) and `star (iˢ) = i⁻ˢ`
(`zmod4Pow_neg`), the conjugate transpose is `i⁻ˢ • P_a = toMat (−s, a) = toMat p⁻¹`. In particular
every `toMat p` is unitary (`toMat p · (toMat p)† = toMat (p · p⁻¹) = toMat 1 = 1`). -/
theorem toMat_inv (p : PauliGroup n) : (p⁻¹).toMat = (p.toMat)ᴴ := by
  rw [toMat, toMat, inv_phase, inv_idx, Matrix.conjTranspose_smul, (pauliString_isHermitian p.idx)]
  congr 1
  exact zmod4Pow_neg p.phase

/-- **The Pauli commutation sign law at the operator level.** For Pauli-group elements `p, q`,
`toMat p · toMat q = (-1)^(pauliAnticommCount p.idx q.idx) • (toMat q · toMat p)`: the phases
`iˢ` are central scalars, so the sign is the phase-free symplectic pairing of the underlying
strings (`pauliString_mul_comm_sign`). -/
theorem toMat_mul_eq_neg_one_pow_smul (p q : PauliGroup n) :
    p.toMat * q.toMat
      = (-1 : ℂ) ^ pauliAnticommCount p.idx q.idx • (q.toMat * p.toMat) := by
  have hpq : p.toMat * q.toMat
      = (zmod4Pow p.phase * zmod4Pow q.phase) • (pauliString p.idx * pauliString q.idx) := by
    simp only [toMat, smul_mul_smul_comm]
  have hqp : q.toMat * p.toMat
      = (zmod4Pow q.phase * zmod4Pow p.phase) • (pauliString q.idx * pauliString p.idx) := by
    simp only [toMat, smul_mul_smul_comm]
  rw [hpq, hqp, pauliString_mul_comm_sign p.idx q.idx, smul_smul, smul_smul]
  congr 1
  ring

/-- **Pauli operators commute or anticommute.** For any two Pauli-group elements `p, q` either
`toMat p · toMat q = toMat q · toMat p` (they commute) or `toMat p · toMat q = -(toMat q · toMat p)`
(they anticommute), according to the parity of the symplectic pairing
(`toMat_mul_eq_neg_one_pow_smul`). -/
theorem toMat_commute_or_anticomm (p q : PauliGroup n) :
    Commute p.toMat q.toMat ∨ p.toMat * q.toMat = -(q.toMat * p.toMat) := by
  rcases Nat.even_or_odd (pauliAnticommCount p.idx q.idx) with he | ho
  · left
    rw [commute_iff_eq, toMat_mul_eq_neg_one_pow_smul, he.neg_one_pow, one_smul]
  · right
    rw [toMat_mul_eq_neg_one_pow_smul, ho.neg_one_pow, neg_one_smul]

/-- **Non-commuting Pauli-group elements have anticommuting operators.** If `p * q ≠ q * p` as group
elements, then their operators anticommute: `toMat p · toMat q = -(toMat q · toMat p)`. (If they
commuted as operators, faithfulness `toMat_injective` would force `p * q = q * p`.) -/
theorem toMat_anticomm_of_ne_mul_comm (p q : PauliGroup n) (h : p * q ≠ q * p) :
    p.toMat * q.toMat = -(q.toMat * p.toMat) := by
  rcases toMat_commute_or_anticomm p q with hc | ha
  · exact absurd (toMat_injective (by rw [toMat_mul, toMat_mul]; exact hc.eq)) h
  · exact ha

/-- The **`n`-qubit Pauli group** structure on `PauliGroup n`. The group axioms are pulled back
through the faithful, multiplicative representation `toMat` into the associative matrix ring:
associativity is `mul_assoc` there, and the inverse law is the involution `pauliString_mul_self`
(`(i⁻ˢ • P_a)(iˢ • P_a) = 1 • I`). -/
instance : Group (PauliGroup n) where
  mul_assoc a b c :=
    toMat_injective (by rw [toMat_mul, toMat_mul, toMat_mul, toMat_mul, mul_assoc])
  one_mul a := toMat_injective (by rw [toMat_mul, toMat_one, one_mul])
  mul_one a := toMat_injective (by rw [toMat_mul, toMat_one, mul_one])
  inv_mul_cancel a := toMat_injective (by
    rw [toMat_mul, toMat_one]
    simp only [toMat, inv_phase, inv_idx]
    rw [smul_mul_smul_comm, pauliString_mul_self, ← zmod4Pow_add, neg_add_cancel, zmod4Pow_zero,
      one_smul])

/-- **The operator of a Pauli-group element is unitary**: `(toMat p)(toMat p)ᴴ = 1`. Since the
adjoint is the inverse (`toMat_inv`), this is `toMat (p · p⁻¹) = toMat 1 = 1`. The `toMat`-interface
form of unitarity, alongside `toMat_mul`/`toMat_one`/`toMat_inv`. -/
theorem toMat_mul_conjTranspose (p : PauliGroup n) : p.toMat * p.toMat.conjTranspose = 1 := by
  rw [← toMat_inv, ← toMat_mul, mul_inv_cancel, toMat_one]

/-- **Odd symplectic pairing ⟹ the Pauli-group elements do not commute.** If
`pauliAnticommCount g.idx p.idx` is odd then `g * p ≠ p * g` as group elements. Their operators
anticommute (`toMat_mul_eq_neg_one_pow_smul`, since `(-1)^odd = -1`), and a nonzero operator cannot
equal its own negation — so were `g, p` to commute as group elements, faithfulness (`toMat_mul`)
would force the unitary `toMat (p * g)` to vanish. This is the parity-indexed group-level converse
of `toMat_anticomm_of_ne_mul_comm`. -/
theorem mul_ne_mul_of_odd_anticommCount {g p : PauliGroup n}
    (hodd : Odd (pauliAnticommCount g.idx p.idx)) : g * p ≠ p * g := by
  intro heq
  have hcomm : g.toMat * p.toMat = p.toMat * g.toMat := by
    rw [← toMat_mul, ← toMat_mul, heq]
  have hanti : g.toMat * p.toMat = -(p.toMat * g.toMat) := by
    rw [toMat_mul_eq_neg_one_pow_smul, hodd.neg_one_pow, neg_one_smul]
  rw [hcomm] at hanti
  have hzero : p.toMat * g.toMat = 0 := by
    have h2 : (2 : ℂ) • (p.toMat * g.toMat) = 0 := by
      rw [two_smul]; nth_rewrite 2 [hanti]; rw [add_neg_cancel]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hunit : (p * g).toMat * ((p * g).toMat)ᴴ = 1 := toMat_mul_conjTranspose (p * g)
  rw [toMat_mul, hzero, Matrix.zero_mul] at hunit
  exact zero_ne_one hunit

/-! ### Finiteness of the Pauli group -/

/-- `PauliGroup n` as the plain product type `ZMod 4 × (Fin n → Fin 4)`, used to transport the
`DecidableEq`/`Fintype` instances (each field of `PauliGroup n` is a finite type with decidable
equality). -/
def equivProd (n : ℕ) : PauliGroup n ≃ ZMod 4 × (Fin n → Fin 4) where
  toFun p := (p.phase, p.idx)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq (PauliGroup n) := (equivProd n).decidableEq

instance : Fintype (PauliGroup n) := Fintype.ofEquiv _ (equivProd n).symm

/-- The faithful matrix representation **as a monoid homomorphism** `pauliRep : PauliGroup n →*
Matrix …`, `(s, a) ↦ iˢ • P_a`. Being an *injective* monoid hom into the operators, it exhibits
`PauliGroup n` as the actual `n`-qubit Pauli group `Gₙ` of Nielsen & Chuang. -/
noncomputable def pauliRep : PauliGroup n →* Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ where
  toFun := toMat
  map_one' := toMat_one
  map_mul' := toMat_mul

@[simp] theorem pauliRep_apply (p : PauliGroup n) :
    pauliRep p = zmod4Pow p.phase • pauliString p.idx := rfl

/-- `pauliRep` is injective (faithfulness), the bundled form of `toMat_injective`. -/
theorem pauliRep_injective : Function.Injective (pauliRep (n := n)) := toMat_injective

/-! ### The total check-row homomorphism -/

/-- The **check row of a Pauli-group element**, the check row of its index (the overall phase `iˢ`
is discarded, as the check matrix records no phase information): `checkRowHom (s, a) = checkRow a`.
Valued in the symplectic space `𝔽₂^{2n} = (Fin n → ZMod 2) × (Fin n → ZMod 2)`. -/
def checkRowHom (p : PauliGroup n) : (Fin n → ZMod 2) × (Fin n → ZMod 2) := checkRow p.idx

@[simp] theorem checkRowHom_apply (p : PauliGroup n) : checkRowHom p = checkRow p.idx := rfl

/-- The check row of the identity is `0` (the all-identity index has vanishing row). -/
theorem checkRowHom_one : checkRowHom (1 : PauliGroup n) = 0 :=
  (checkRow_eq_zero_iff (0 : Fin n → Fin 4)).mpr rfl

/-- **The total check-row homomorphism law** (Nielsen & Chuang §10.5.1, for the full Pauli group):
`r(p q) = r(p) + r(q)`, i.e. "addition in the row representation corresponds to multiplication of
group elements". The phase is irrelevant to the row, so this is the index-level additivity
`checkRow_pauliMulIndex`. -/
theorem checkRowHom_mul (p q : PauliGroup n) :
    checkRowHom (p * q) = checkRowHom p + checkRowHom q := by
  simp only [checkRowHom, mul_idx, checkRow_pauliMulIndex]

/-- **The bare kernel of the check row**: `r(p) = 0 ↔ p.idx = 0`, i.e. `checkRowHom p` vanishes
exactly when `p` is a phase-only element `iˢ · I`. From the trivial kernel of `checkRow`
(`checkRow_eq_zero_iff`). (Restricting to a subgroup `S` with `-I ∉ S` upgrades this to a *trivial*
kernel `r(p) = 0 → p = 1`; developed downstream.) -/
theorem checkRowHom_eq_zero_iff (p : PauliGroup n) : checkRowHom p = 0 ↔ p.idx = 0 :=
  checkRow_eq_zero_iff p.idx

/-! ### The element `-I` -/

/-- The Pauli-group element **`-I`**, i.e. `(2, 0)` (`i² · I = -I`). Its non-membership `negOne ∉ S`
in a subgroup `S` is the standing hypothesis `-I ∉ S` of Nielsen & Chuang Proposition 10.3. -/
def negOne (n : ℕ) : PauliGroup n := ⟨2, 0⟩

/-- The representation of `negOne` is the operator `-I` (`-1` in the matrix ring): `i² • P₀ =
(-1) • I = -I`. -/
theorem pauliRep_negOne : pauliRep (negOne n) = -1 := by
  simp only [pauliRep_apply, negOne]
  rw [zmod4Pow_two, neg_one_smul, (pauliString_eq_one_iff (0 : Fin n → Fin 4)).mpr rfl]

/-- `negOne` has vanishing check row (it is a phase-only element). -/
theorem checkRowHom_negOne : checkRowHom (negOne n) = 0 :=
  checkRow_eq_zero_iff (0 : Fin n → Fin 4) |>.mpr rfl

end PauliGroup

end CliffordCSS

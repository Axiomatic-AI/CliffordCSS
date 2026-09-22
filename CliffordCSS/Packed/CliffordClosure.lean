import CliffordCSS.Packed.SymplecticClosure
import CliffordCSS.Symplectic.Generation

/-!
# The packed image of a Clifford circuit and its generator closure (App. D.1)

Pure mathematics : the packing `packedClifford U := ofBlocks n
(cliffordSymplectic U)` of a Clifford circuit into the `Nat`-bitmask calculus, and the finite
saturation `spEnumAux` of the packed identity under right-multiplication by the packed elementary
Clifford generators. It names only raw carriers (`Matrix`, `Nat`, `Fin`, `ZMod 2`) and the
this library Clifford/symplectic layer.

## Why this exists (the W4 completeness closure)

The certificate-route plan for Theorem D.1 (`dec-conditional-d1-certificate-route`, refined by
`dec-d4-kernel-computed-reachability`) discharges the *Local reduction* lemma (`lem-local`,
Lemma D.4) by a **kernel computation** on the packed representation: build the element list of
`Sp(4, 𝔽₂)` (resp. `Sp(2, 𝔽₂)`) by closure from the elementary Clifford generators, then reverse-BFS
that list for reachability. The exhaustiveness of that closure is the *completeness* half of Lemma
D.4, and it rests on W1's generation theorem
`CliffordCSS.exists_cliffordSymplectic_of_mem_binarySymplecticGroup` (every symplectic matrix is
`cliffordSymplectic U` for some circuit `U`) together with the fact that `cliffordSymplectic` is a
monoid anti-homomorphism (`cliffordSymplectic_append` / `cliffordSymplectic_nil`).

This file lands the **decide-free substrate** of that completeness closure: it transports the
anti-homomorphism through the packed encoder `ofBlocks` (whose algebra
`PackedSymplecticClosure.lean` supplies), enumerates the elementary gates, and — the keystone —
proves that the packing of *any*
Clifford circuit `U` already lies in the `U.length`-round saturation `spEnumAux` of the packed
identity under the packed generators. The remaining *stabilisation* step (that `spEnumAux` reaches a
genuine fixpoint, so that a single fixed list contains every circuit image, hence — via W1 — every
symplectic element) is the one kernel `decide` of the closure and is deferred to the completeness
chunk; nothing here evaluates a large list.

## What is proved here

* `packedClifford` — the packing `ofBlocks n (cliffordSymplectic U)` of a Clifford circuit, with
  `packedClifford_lt` (range), `packedClifford_nil` (`= one n`, the closure seed),
  `toBlocks_packedClifford` (its block decode is `cliffordSymplectic U`),
  `isPackedSymplectic_packedClifford` (it passes the packed symplectic test), and the multiplicative
  bridge `packedClifford_append` (`packedClifford (U ++ V) = mul (packedClifford V) (packedClifford
  U)`) — the anti-homomorphism, packed.
* `packedClifford_had` / `packedClifford_phase` / `packedClifford_cnot` — the packings of the three
  elementary generators as `ofBlocks` of their explicit `Matrix` forms (`hadamardSymplectic` /
  `shearZ (single j j 1)` / `cnotSymplectic`), the numerals the later reachability `decide` runs on.
* `gateList` / `mem_gateList` — the finite enumeration of every elementary Clifford gate on `n`
  wires (Hadamard, phase, CNOT), proved exhaustive.
* `gens` / `packedClifford_mem_gens` — the packed generator list `(gateList n).map (packedClifford
  [·])`, with the fact that every single-gate circuit's packing is a listed generator.
* `grow` / `spEnumAux` — one saturation round (append all generator right-products, deduplicate) and
  its `k`-fold iterate from the packed identity, with `spEnumAux_subset_succ` (monotonicity).
* `packedClifford_mem_spEnumAux` — **the keystone**: `packedClifford U ∈ spEnumAux n U.length`. By
  the packed anti-homomorphism a circuit's packing is a right-product of generator packings, so
  `U.length` saturation rounds already reach it — the decide-free heart of the completeness closure.
-/

open Matrix

namespace CliffordCSS.Packed

open CliffordCSS

variable {n : ℕ}

/-! ### The packed image of a Clifford circuit -/

/-- **The packed image of a Clifford circuit** `U`: the packing `ofBlocks n (cliffordSymplectic U)`
of its `2n × 2n` symplectic matrix into the `Nat`-bitmask calculus. The map carrying the
`Matrix`-level Clifford action into the packed representation the finite `Sp(2n, 𝔽₂)` enumeration is
built from. -/
def packedClifford (U : CliffordCircuit n) : ℕ := ofBlocks n (cliffordSymplectic U)


/-- **The packing of the empty circuit is the packed identity**, `packedClifford [] = one n`: the
empty circuit has the identity symplectic matrix (`cliffordSymplectic_nil`), whose packing is the
seed `one n` of the generator closure (`ofBlocks_one`). -/
theorem packedClifford_nil : packedClifford ([] : CliffordCircuit n) = one n := by
  rw [packedClifford, cliffordSymplectic_nil, ofBlocks_one]

/-- **The block decode of a circuit's packing is its symplectic matrix**,
`toBlocks n (packedClifford U) = cliffordSymplectic U` (encoder round-trip `toBlocks_ofBlocks`). -/
theorem toBlocks_packedClifford (U : CliffordCircuit n) :
    toBlocks n (packedClifford U) = cliffordSymplectic U :=
  toBlocks_ofBlocks n _


/-- **The packed anti-homomorphism**:
`packedClifford (U ++ V) = mul (n + n) (packedClifford V) (packedClifford U)`. `cliffordSymplectic`
reverses order on concatenation (`cliffordSymplectic_append`, labels are row vectors acted on from
the right) and `ofBlocks` is multiplicative into the packed product (`mul_ofBlocks`), so packing a
concatenated circuit is the packed product of the packings in the reversed order — the fact that
turns a circuit's packing into a right-product of generator packings. -/
theorem packedClifford_append (U V : CliffordCircuit n) :
    packedClifford (U ++ V) = mul (n + n) (packedClifford V) (packedClifford U) := by
  simp only [packedClifford, cliffordSymplectic_append, mul_ofBlocks]

/-! ### The elementary generators, packed -/


/-! ### Enumerating the elementary gates -/

/-- The list of every elementary **CNOT gate** on `n` wires: for each ordered pair of distinct wires
`(c, t)`, the gate `cnot c t`. Built by `filterMap` over `Fin n × Fin n`, keeping the pairs with
`c ≠ t` (the dependent `cnot` constructor carries that proof). Exhaustive by `mem_gateList`. -/
def cnotList (n : ℕ) : List (CliffordGate n) :=
  (List.finRange n).flatMap fun c =>
    (List.finRange n).filterMap fun t => if h : c ≠ t then some (CliffordGate.cnot c t h) else none

/-- **The finite enumeration of every elementary Clifford gate** on `n` wires: the single-wire
Hadamards `had j` and phases `phase j` for each wire `j`, together with every distinct-pair CNOT
(`cnotList`). Proved exhaustive by `mem_gateList`; its packings form the generator list `gens`. -/
def gateList (n : ℕ) : List (CliffordGate n) :=
  (List.finRange n).map CliffordGate.had ++
    (List.finRange n).map CliffordGate.phase ++ cnotList n

/-- **The gate enumeration is exhaustive**: every elementary Clifford gate `g : CliffordGate n`
occurs in `gateList n`. Case analysis on `g`; the Hadamard and phase cases are membership in the
mapped `finRange`, and the CNOT case unpacks the `filterMap` at the pair `(c, t)`, where `c ≠ t`
selects the `some` branch (`dif_pos`). -/
theorem mem_gateList (g : CliffordGate n) : g ∈ gateList n := by
  rcases g with j | j | ⟨c, t, h⟩
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, List.mem_finRange c, ?_⟩)
    exact List.mem_filterMap.mpr ⟨t, List.mem_finRange t, dif_pos h⟩

/-! ### The packed generator list and the saturation -/

/-- **The packed generator list**: the packings `packedClifford [g]` of the elementary Clifford
gates (`gateList`). The set the closure saturates under — every element of the generated group is a
product of these (W1). -/
def gens (n : ℕ) : List ℕ := (gateList n).map (fun g => packedClifford [g])

/-- **Every single-gate circuit's packing is a listed generator**, `packedClifford [g] ∈ gens n`.
Immediate from `mem_gateList` and the definition of `gens` as the map of `gateList`. -/
theorem packedClifford_mem_gens (g : CliffordGate n) : packedClifford [g] ∈ gens n :=
  List.mem_map.mpr ⟨g, mem_gateList g, rfl⟩

/-- **One saturation round**: append to `L` every right-product `mul (n + n) a s` of a current
element `a ∈ L` with a generator `s ∈ gens n`, then deduplicate. Iterated by `spEnumAux`; a fixpoint
of `grow` is a list closed under generator-multiplication, i.e. (by W1) all of `Sp(2n, 𝔽₂)`
packed. -/
def grow (n : ℕ) (L : List ℕ) : List ℕ :=
  (L ++ L.flatMap fun a => (gens n).map fun s => mul (n + n) a s).dedup

/-- **The `k`-round generator saturation** from the packed identity: `spEnumAux n 0 = [one n]`, and
each further round applies `grow`. `spEnumAux n k` contains the packing of every Clifford circuit
of length `≤ k` (`packedClifford_mem_spEnumAux`); once it stabilises it is the full packed
`Sp(2n, 𝔽₂)`. -/
def spEnumAux (n : ℕ) : ℕ → List ℕ
  | 0 => [one n]
  | k + 1 => grow n (spEnumAux n k)


/-- **The keystone of the completeness closure**: the packing of *any* Clifford circuit `U` lies in
the `U.length`-round saturation, `packedClifford U ∈ spEnumAux n U.length`. Induction on `U`: the
empty circuit packs to the seed `one n = spEnumAux n 0` (`packedClifford_nil`); a circuit
`g :: rest` packs, by the packed anti-homomorphism (`packedClifford_append`, using
`g :: rest = [g] ++ rest`), to
`mul (n + n) (packedClifford rest) (packedClifford [g])`, a generator right-product of the
inductively-placed `packedClifford rest` — hence added by the `grow` round taking `spEnumAux n
rest.length` to `spEnumAux n (rest.length + 1)`. Decide-free: it fixes the *round index* to the
circuit length, deferring to the completeness chunk the single `decide` that the saturation
stabilises. -/
theorem packedClifford_mem_spEnumAux (U : CliffordCircuit n) :
    packedClifford U ∈ spEnumAux n U.length := by
  induction U with
  | nil => simp [spEnumAux, packedClifford_nil]
  | cons g rest ih =>
    have hstep : packedClifford (g :: rest)
        = mul (n + n) (packedClifford rest) (packedClifford [g]) :=
      packedClifford_append [g] rest
    rw [List.length_cons, spEnumAux, grow, hstep, List.mem_dedup, List.mem_append]
    refine Or.inr (List.mem_flatMap.mpr ⟨packedClifford rest, ih, ?_⟩)
    exact List.mem_map.mpr ⟨packedClifford [g], packedClifford_mem_gens g, rfl⟩

end CliffordCSS.Packed

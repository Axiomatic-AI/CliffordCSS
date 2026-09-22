import CliffordCSS.Packed.Reaches
import CliffordCSS.Packed.CliffordCompleteness
import CliffordCSS.DepthOne.LocalReindex

/-!
# Lemma D.4 at width two — `LocalReduction 2 3` (Beyond transversality, App. D.1)

Pure mathematics : the **terminal assembly** of Lemma D.4
(*Local reduction*, `lem-local`) of *Beyond transversality* (arXiv:2608.05688) at width two —
`LocalReduction 2 3`, "every element of `Sp(4, 𝔽₂)` reaches a terminal block in at most three
moves". It names only raw carriers (`Matrix`, `Nat`) and the this library symplectic/reachability
layer.

## What this file assembles (work item W4, TERMINAL)

The width-one clause `LocalReduction 1 1` (`Sp(2, 𝔽₂)`) is already proved
(`CliffordCSS.localReduction_width_one`). This file discharges the remaining width-two clause by
feeding the two halves of the packed kernel computation into one another:

* **completeness** (`CliffordCSS.Packed.exists_mem_spEnumSp4`): every `M ∈ Sp(4, 𝔽₂)` is the packed
  decode `toBlocks 2 a` of some `a` in the closed generator enumeration `spEnumSp4`;
* **packed reachability** (`spEnumSp4_packedReaches`, below): every `a ∈ spEnumSp4` satisfies
  `packedReaches 2 3 a` — reaches a packed terminal block in at most three packed moves — a kernel
  `decide`;
* **soundness** (`CliffordCSS.Packed.reachesTerminalIn_toBlocks_of_packedReaches`): a packed reach
  decodes to a genuine `Matrix` reach `ReachesTerminalIn 3 (toBlocks 2 a)`.

Chaining them gives `localReduction_fin_two`: every `g ∈ Sp(4, 𝔽₂)` on the concrete index type
`Fin 2` satisfies `ReachesTerminalIn 3 g`. The abstract-index transport (T2, the reindex
invariances of `CliffordCSS/DepthOne/LocalReindex.lean`) then lifts it to
`LocalReduction 2 3`, which quantifies over *every* index type of cardinality two: for arbitrary
`κ` with `Fintype.card κ = 2`, the bijection `e := Fintype.equivFinOfCardEq` carries the block `g`
to the `Fin 2` block `reSp e g`, and `mem_binarySymplecticGroup_reSp` / `reachesTerminalIn_reSp`
turn the `Fin 2` verification back into the statement at `κ`.

## Why the reachability `decide` is split into `24` declarations

`spEnumSp4_packedReaches` is the reverse-BFS reachability check of Lemma D.4 — the paper's single
machine-checked step — run natively on the packed `Nat` calculus. It is a genuine kernel hot spot,
and its **memory** footprint is the binding constraint: a monolithic
`decide (∀ a ∈ spEnumSp4, packedReaches 2 3 a)` folds all `720` bounded searches into one kernel
reduction whose peak resident set grows linearly with the number of elements (measured at
~`0.5` GB per element, ~`30` GB already at `60` elements), so the full list would need hundreds of
gigabytes and thrash. Splitting the check into `24` separate `30`-element declarations
(`reachChunk0 … reachChunk23`) bounds each kernel reduction to one `30`-element window (~`16` GB,
freed at the declaration boundary), keeping the peak flat while the total kernel work is unchanged.
The windows are the consecutive `30`-blocks `(spEnumSp4.drop (30 * i)).take 30`, reassembled into
the statement over the whole list by `List.forall_mem_append`, with no re-evaluation of
`packedReaches`. `native_decide` is barred (numerics policy); every chunk is a real kernel `decide`
under a raised `maxHeartbeats` / `maxRecDepth`. No `sorry`, no new axiom (all reduce to
`{propext, Classical.choice, Quot.sound}`).

This is the terminal chunk of W4: together with the completeness half and the width-one clause
`localReduction_width_one`, it discharges Lemma D.4's **reduction (reachability) clauses**
`LocalReduction 1 1 ∧ LocalReduction 2 3` in the kernel — and thereby the `⊆` direction of Theorem
D.1's Eq. D3, which needs only the reduction. Lemma D.4's terminal-*count* clauses are a separate
concern: the Sp(2) count is `CliffordCSS.terminalBlocks_width_one`.
-/

open Matrix

namespace CliffordCSS.Packed

section ReverseBfsReachability

-- The reachability check below is run natively on the packed `Nat` calculus, so its kernel
-- recursion is deep; the budget is raised for the whole section (`maxRecDepth` is unrestricted).
set_option maxRecDepth 1000000

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 0: the elements at positions 0–29 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk0 : ∀ a ∈ (spEnumSp4.drop 0).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 1: the elements at positions 30–59 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk1 : ∀ a ∈ (spEnumSp4.drop 30).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 2: the elements at positions 60–89 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk2 : ∀ a ∈ (spEnumSp4.drop 60).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 3: the elements at positions 90–119 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk3 : ∀ a ∈ (spEnumSp4.drop 90).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 4: the elements at positions 120–149 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk4 : ∀ a ∈ (spEnumSp4.drop 120).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 5: the elements at positions 150–179 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk5 : ∀ a ∈ (spEnumSp4.drop 150).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 6: the elements at positions 180–209 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk6 : ∀ a ∈ (spEnumSp4.drop 180).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 7: the elements at positions 210–239 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk7 : ∀ a ∈ (spEnumSp4.drop 210).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 8: the elements at positions 240–269 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk8 : ∀ a ∈ (spEnumSp4.drop 240).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 9: the elements at positions 270–299 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk9 : ∀ a ∈ (spEnumSp4.drop 270).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 10: the elements at positions 300–329 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk10 : ∀ a ∈ (spEnumSp4.drop 300).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 11: the elements at positions 330–359 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk11 : ∀ a ∈ (spEnumSp4.drop 330).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 12: the elements at positions 360–389 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk12 : ∀ a ∈ (spEnumSp4.drop 360).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 13: the elements at positions 390–419 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk13 : ∀ a ∈ (spEnumSp4.drop 390).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 14: the elements at positions 420–449 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk14 : ∀ a ∈ (spEnumSp4.drop 420).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 15: the elements at positions 450–479 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk15 : ∀ a ∈ (spEnumSp4.drop 450).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 16: the elements at positions 480–509 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk16 : ∀ a ∈ (spEnumSp4.drop 480).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 17: the elements at positions 510–539 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk17 : ∀ a ∈ (spEnumSp4.drop 510).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 18: the elements at positions 540–569 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk18 : ∀ a ∈ (spEnumSp4.drop 540).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 19: the elements at positions 570–599 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk19 : ∀ a ∈ (spEnumSp4.drop 570).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 20: the elements at positions 600–629 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk20 : ∀ a ∈ (spEnumSp4.drop 600).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 21: the elements at positions 630–659 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk21 : ∀ a ∈ (spEnumSp4.drop 630).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 22: the elements at positions 660–689 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk22 : ∀ a ∈ (spEnumSp4.drop 660).take 30, packedReaches 2 3 a := by
  decide

set_option maxHeartbeats 4000000000 in
-- Kernel reverse-BFS reachability decide (Lemma D.4); native_decide barred; see module docstring.
/-- Reachability chunk 23: the elements at positions 690–719 of `spEnumSp4` each reach a packed
terminal block in at most three packed moves (`packedReaches 2 3`). One `30`-element window of
the reverse-BFS check of Lemma D.4, kept a separate declaration to bound the kernel `decide`'s
peak memory (see the module docstring). -/
theorem reachChunk23 : ∀ a ∈ (spEnumSp4.drop 690).take 30, packedReaches 2 3 a := by
  decide

/-- **Packed reachability over all of `Sp(4, 𝔽₂)`**: every `a ∈ spEnumSp4` reaches a packed
terminal block in at most three packed moves. The reverse-BFS reachability half of Lemma D.4,
assembled from the `24` memory-bounded `30`-element chunks `reachChunk0 … reachChunk23` (the
consecutive `30`-blocks of `spEnumSp4`) by `List.forall_mem_append`; the append equation is a
definitional list identity (no `packedReaches` re-evaluation). Fed, through
`reachesTerminalIn_toBlocks_of_packedReaches`, into `LocalReduction 2 3`. -/
theorem spEnumSp4_packedReaches : ∀ a ∈ spEnumSp4, packedReaches 2 3 a := by
  have e : spEnumSp4 =
      (spEnumSp4.drop 0).take 30 ++
        ((spEnumSp4.drop 30).take 30 ++
        ((spEnumSp4.drop 60).take 30 ++
        ((spEnumSp4.drop 90).take 30 ++
        ((spEnumSp4.drop 120).take 30 ++
        ((spEnumSp4.drop 150).take 30 ++
        ((spEnumSp4.drop 180).take 30 ++
        ((spEnumSp4.drop 210).take 30 ++
        ((spEnumSp4.drop 240).take 30 ++
        ((spEnumSp4.drop 270).take 30 ++
        ((spEnumSp4.drop 300).take 30 ++
        ((spEnumSp4.drop 330).take 30 ++
        ((spEnumSp4.drop 360).take 30 ++
        ((spEnumSp4.drop 390).take 30 ++
        ((spEnumSp4.drop 420).take 30 ++
        ((spEnumSp4.drop 450).take 30 ++
        ((spEnumSp4.drop 480).take 30 ++
        ((spEnumSp4.drop 510).take 30 ++
        ((spEnumSp4.drop 540).take 30 ++
        ((spEnumSp4.drop 570).take 30 ++
        ((spEnumSp4.drop 600).take 30 ++
        ((spEnumSp4.drop 630).take 30 ++
        ((spEnumSp4.drop 660).take 30 ++
        ((spEnumSp4.drop 690).take 30))))))))))))))))))))))) := by
    rfl
  rw [e]
  simp only [List.forall_mem_append]
  exact ⟨reachChunk0, reachChunk1, reachChunk2, reachChunk3, reachChunk4, reachChunk5,
    reachChunk6, reachChunk7, reachChunk8, reachChunk9, reachChunk10, reachChunk11,
    reachChunk12, reachChunk13, reachChunk14, reachChunk15, reachChunk16, reachChunk17,
    reachChunk18, reachChunk19, reachChunk20, reachChunk21, reachChunk22, reachChunk23⟩

end ReverseBfsReachability

end CliffordCSS.Packed

namespace CliffordCSS

/-- **Lemma D.4 at width two, over the concrete index type `Fin 2`**: every `g ∈ Sp(4, 𝔽₂)` on
`Fin 2 ⊕ Fin 2` reaches a terminal block in at most three moves. Completeness
(`Packed.exists_mem_spEnumSp4`) writes `g` as the packed decode `toBlocks 2 a` of some
`a ∈ spEnumSp4`; the packed reachability `Packed.spEnumSp4_packedReaches` gives
`packedReaches 2 3 a`; and its soundness `Packed.reachesTerminalIn_toBlocks_of_packedReaches`
decodes that to `ReachesTerminalIn 3 (toBlocks 2 a) = ReachesTerminalIn 3 g`. -/
theorem localReduction_fin_two (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hg : g ∈ binarySymplecticGroup (Fin 2)) : ReachesTerminalIn 3 g := by
  obtain ⟨a, ha, rfl⟩ := Packed.exists_mem_spEnumSp4 hg
  exact Packed.reachesTerminalIn_toBlocks_of_packedReaches 3 a (Packed.spEnumSp4_packedReaches a ha)

universe u

/-- **Lemma D.4 (Local reduction) at width two: `LocalReduction 2 3`.** "Every element of
`Sp(4, 𝔽₂)` reaches a terminal block in at most three moves", stated — as in the paper — over an
*arbitrary* cell index type `κ` of cardinality two, not just `Fin 2`. The concrete `Fin 2`
verification `localReduction_fin_two` is transported to `κ` along the bijection
`e := Fintype.equivFinOfCardEq` by the reindex invariances of
`CliffordCSS/DepthOne/LocalReindex.lean`: `mem_binarySymplecticGroup_reSp` carries the
symplectic hypothesis to the relabelled block `reSp e g`, and `reachesTerminalIn_reSp` carries the
resulting reachability back to `g`. Together with `localReduction_width_one` this discharges Lemma
D.4's reduction (reachability) clauses `LocalReduction 1 1 ∧ LocalReduction 2 3` in the kernel; its
terminal-count clauses are separate (Sp(2): `terminalBlocks_width_one`. -/
theorem localReduction_width_two : LocalReduction.{u} 2 3 := by
  intro κ _ _ hcard g hg
  let e := Fintype.equivFinOfCardEq hcard
  exact (reachesTerminalIn_reSp e 3 g).mp
    (localReduction_fin_two (reSp e g) ((mem_binarySymplecticGroup_reSp e g).mpr hg))

end CliffordCSS

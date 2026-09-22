import CliffordCSS.Packed.CliffordCompleteness
import CliffordCSS.Packed.TerminalBlock
import CliffordCSS.DepthOne.LocalMove

/-!
# Lemma D.4's width-two count clause — `Sp(4, 𝔽₂)` has exactly sixteen terminal blocks

Pure mathematics : the **count clause of *Beyond transversality*
(arXiv:2608.05688) Lemma D.4 (*Local reduction*, `lem-local`) at width two** — "there are sixteen
terminal blocks" for `Sp(4, 𝔽₂)`. It names only raw carriers (`Matrix`, `Nat`, `Fin`, `ZMod 2`) and
the this library symplectic/terminal layer.

## The statement and why it is a genuine cardinality

`terminalBlocks_width_two` is the width-two analogue of `terminalBlocks_width_one` (which pins the
`Sp(2, 𝔽₂)` terminal set as the two-element `{1, symplecticMatrix}`): the **set** of blocks
`g ∈ Sp(4, 𝔽₂)` that are terminal (`IsTerminalLayer`) has `Set.ncard` equal to `16`. This is the
`ncard` of the actual terminal *set* of matrices — not a bare list length: a `List.countP` over the
packed enumeration would prove only that sixteen *packed reps* pass the terminal test, which without
no-duplicates + injectivity of the block decode could be fewer than sixteen distinct matrices. The
faithful cardinality is recovered here by a nodup/injectivity/completeness bridge over the packed
enumeration (the anti-weakening obligation of `CLAUDE.md`).

## How it is proved (packed enumeration, kernel `decide`)

The completeness half of Lemma D.4 (`PackedCliffordCompleteness.lean`) enumerates `Sp(4, 𝔽₂)` as the
`720` packed `Nat` representatives `spEnumSp4`, with `exists_mem_spEnumSp4` asserting every
symplectic matrix is the block-decode `toBlocks 2 a` of some `a ∈ spEnumSp4`. Filtering that list by
the packed terminal predicate `IsPackedTerminal 2` (`PackedTerminalBlock.lean`) gives `termEnumSp4`;
four one-line kernel `decide`s establish that

* `spEnumSp4` has no duplicates (`spEnumSp4_nodup`) and lands in range (`spEnumSp4_lt`),
* every listed element is symplectic (`spEnumSp4_isPackedSymplectic`), and
* the filtered list has length `16` (`termEnumSp4_length`) — the paper's number, machine-confirmed.

The terminal set is then exhibited as the injective image `toBlocks 2 '' termEnumSp4`: forward, a
terminal symplectic `g` is `toBlocks 2 a` for some listed `a` (completeness) which then passes the
packed terminal test (`isPackedTerminal_iff_isTerminalLayer`); backward, each listed representative
decodes to a symplectic (`isPackedSymplectic_iff_mem`) terminal
(`isPackedTerminal_iff_isTerminalLayer`) block. Injectivity of `toBlocks 2` on the range
(`toBlocks_inj_of_lt`, fed by `spEnumSp4_lt`) turns the image cardinality into the list length, and
no-duplicates turns that into `16`.

No `sorry`, no new `axiom`, no `native_decide` (barred by the project numerics policy); the
`decide`s are genuine kernel evaluations on `Nat` bitmasks. Axioms reduce to
`{propext, Classical.choice, Quot.sound}`.
-/

open Matrix

namespace CliffordCSS.Packed

-- The kernel `decide`s over the `720`-element packed enumeration recurse deeply; a raised recursion
-- budget (section-wide is accepted by Mathlib's `setOptionLinter`, unlike `maxHeartbeats`) covers
-- the packed lemmas here.
set_option maxRecDepth 1000000

/-- **The packed terminal representatives of `Sp(4, 𝔽₂)`**: the sublist of the `720` packed reps
`spEnumSp4` that pass the packed terminal-block test `IsPackedTerminal 2` (Eq. (d1-term), packed).
Its length is `16` (`termEnumSp4_length`), and — being a sublist of the duplicate-free `spEnumSp4`
whose decode is injective — it names exactly the sixteen distinct terminal blocks of `Sp(4, 𝔽₂)`. -/
def termEnumSp4 : List ℕ := spEnumSp4.filter (fun a => decide (IsPackedTerminal 2 a))

set_option maxHeartbeats 4000000000 in
-- A kernel `decide` over the `720`-element packed enumeration (its `Nodup` is an `O(720²)` sweep of
-- pairwise `Nat` disequalities); it needs a raised heartbeat budget. `native_decide` is barred by
-- the numerics policy, so this is a real kernel evaluation.
/-- **`spEnumSp4` lists its `720` packed representatives without duplicates.** A kernel `decide`
over the explicit `Nat` literals; needed so the image cardinality of the terminal sublist equals
its length. -/
theorem spEnumSp4_nodup : spEnumSp4.Nodup := by decide

set_option maxHeartbeats 4000000000 in
-- A kernel `decide` evaluating `< 2 ^ 16` on each of the `720` reps; it needs a raised heartbeat
-- budget. `native_decide` is barred by the numerics policy.
/-- **Every packed representative of `spEnumSp4` lies in the width-two enumeration range**,
`a < 2 ^ ((2 + 2) * (2 + 2)) = 2 ^ 16`. A kernel `decide`; the in-range hypothesis
`toBlocks_inj_of_lt` needs to conclude injectivity of the block decode on the listed reps. -/
theorem spEnumSp4_lt : ∀ a ∈ spEnumSp4, a < 2 ^ ((2 + 2) * (2 + 2)) := by decide

set_option maxHeartbeats 4000000000 in
-- A kernel `decide` evaluating the packed symplectic test (`Gᵀ J G = J` in the `Nat` calculus) on
-- each of the `720` reps; it needs a raised heartbeat budget. `native_decide` is barred by the
-- numerics policy.
/-- **Every packed representative of `spEnumSp4` passes the packed symplectic test.** A kernel
`decide`; combined with `isPackedSymplectic_iff_mem` it certifies that each listed representative
decodes to a genuine element of `Sp(4, 𝔽₂)` (the backward inclusion of the terminal set). -/
theorem spEnumSp4_isPackedSymplectic : ∀ a ∈ spEnumSp4, IsPackedSymplectic 2 a := by decide

set_option maxHeartbeats 4000000000 in
-- A kernel `decide` evaluating the packed terminal predicate on each of the `720` reps and counting
-- the sublist length; it needs a raised heartbeat budget. `native_decide` is barred by the numerics
-- policy.
/-- **There are exactly sixteen packed terminal representatives.** The filtered list `termEnumSp4`
has length `16` — the paper's count "there are sixteen terminal blocks", decided in the kernel by
evaluating the packed terminal predicate on each of the `720` reps. -/
theorem termEnumSp4_length : termEnumSp4.length = 16 := by decide

/-- Membership in `termEnumSp4`: a packed rep is listed exactly when it is one of the `720`
representatives and passes the packed terminal test. -/
theorem mem_termEnumSp4 {a : ℕ} : a ∈ termEnumSp4 ↔ a ∈ spEnumSp4 ∧ IsPackedTerminal 2 a := by
  simp [termEnumSp4, List.mem_filter]

/-- `termEnumSp4` inherits no-duplicates from `spEnumSp4` (a filtered duplicate-free list is
duplicate-free). -/
theorem termEnumSp4_nodup : termEnumSp4.Nodup := spEnumSp4_nodup.filter _

end CliffordCSS.Packed

namespace CliffordCSS

open CliffordCSS.Packed

set_option maxRecDepth 1000000 in
/-- **Lemma D.4's count clause at width two: "there are sixteen terminal blocks".** The terminal
blocks of `Sp(4, 𝔽₂)` — the symplectic matrices `g` satisfying the six-fold vanishing predicate
`IsTerminalLayer` (Eq. (d1-term)) — form a set of cardinality exactly `16`.

The terminal set is the injective image `toBlocks 2 '' termEnumSp4` of the sixteen packed terminal
representatives: completeness of the packed enumeration (`exists_mem_spEnumSp4`) gives the forward
inclusion, the packed symplectic/terminal faithfulness bridges
(`isPackedSymplectic_iff_mem`, `isPackedTerminal_iff_isTerminalLayer`) the backward one, and
injectivity of the block decode on the range (`toBlocks_inj_of_lt`) plus no-duplicates
(`termEnumSp4_nodup`) turn the image cardinality into the list length `termEnumSp4_length = 16`.
This is the width-two companion of `terminalBlocks_width_one` ("there are two terminal blocks"). -/
theorem terminalBlocks_width_two :
    {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) |
      g ∈ binarySymplecticGroup (Fin 2) ∧ IsTerminalLayer g}.ncard = 16 := by
  have hset :
      {g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) |
        g ∈ binarySymplecticGroup (Fin 2) ∧ IsTerminalLayer g}
        = toBlocks 2 '' {a | a ∈ termEnumSp4} := by
    ext g
    constructor
    · rintro ⟨hg, hterm⟩
      obtain ⟨a, ha, rfl⟩ := exists_mem_spEnumSp4 hg
      exact ⟨a, mem_termEnumSp4.mpr ⟨ha, (isPackedTerminal_iff_isTerminalLayer 2 a).mpr hterm⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨ha1, ha2⟩ := mem_termEnumSp4.mp ha
      exact ⟨(isPackedSymplectic_iff_mem 2 a).mp (spEnumSp4_isPackedSymplectic a ha1),
        (isPackedTerminal_iff_isTerminalLayer 2 a).mp ha2⟩
  have hinj : Set.InjOn (toBlocks 2) {a | a ∈ termEnumSp4} := by
    intro a ha b hb hab
    exact toBlocks_inj_of_lt (spEnumSp4_lt a (mem_termEnumSp4.mp ha).1)
      (spEnumSp4_lt b (mem_termEnumSp4.mp hb).1) hab
  have hcoe : {a | a ∈ termEnumSp4} = (termEnumSp4.toFinset : Set ℕ) := by
    ext a; simp
  rw [hset, hinj.ncard_image, hcoe, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup termEnumSp4_nodup, termEnumSp4_length]

end CliffordCSS

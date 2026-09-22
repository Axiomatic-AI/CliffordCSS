import CliffordCSS.Packed.BlockMove
import CliffordCSS.Packed.TerminalBlock

/-!
# Packed bounded reachability (Beyond transversality, App. D.1 — Lemma D.4)

Pure mathematics : the **packed `Nat` bounded reachability**
predicate of *Beyond transversality* (arXiv:2608.05688) — the packed mirror of the `Matrix`-level
`ReachesTerminalIn` of `CliffordCSS/DepthOne/LocalMove.lean` — proved *sound* against it
under the packed decoder `toBlocks`. It names only raw carriers (`Matrix`, `Nat`) and the this library
reachability/move/terminal relations (`ReachesTerminalIn`, `IsBlockMove`, `IsTerminalLayer`).

## Why this exists (the reachability half of Lemma D.4)

The *Local reduction* lemma (`lem-local`, Lemma D.4) is discharged by a **kernel computation** on
the packed representation (`dec-d4-kernel-computed-reachability`): a bounded breadth-first search
from the terminal set over the enumerated element list of `Sp(4, 𝔽₂)` (resp. `Sp(2, 𝔽₂)`). The
completeness half is landed (`CliffordCSS/Packed/CliffordCompleteness.lean`); the previous reachability
chunks landed the packed terminal predicate (`IsPackedTerminal`,
`CliffordCSS/Packed/TerminalBlock.lean`) and the packed one-move neighbour list with its soundness
bridge (`packedNeighbors` / `packedNeighbors_sound`, `CliffordCSS/Packed/BlockMove.lean`). **This file
assembles those into the bounded search itself.**

The search must run *in the packed calculus* — the kernel evaluates the move expansions natively on
`Nat` bitmasks rather than on the function-type carrier
`Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)` (measured intractable — see
`CliffordCSS/Packed/BinaryMatrix.lean`) — but its conclusion must be a *statement about `Matrix`
blocks*, since Lemma D.4 (`LocalReduction`) quantifies over `binarySymplecticGroup` elements. So:

* `packedReaches n k a` — the packed predicate "block `a` reaches a terminal block in at most `k`
  packed moves", defined by structural recursion on `k` exactly as `ReachesTerminalIn`: terminality
  `IsPackedTerminal n a` at `k = 0`, and "terminal, or some neighbour reaches terminal in `k - 1`
  moves" at `k + 1`, where the neighbours are the finite packed list `packedNeighbors n a`. Because
  that list is a `List` (not an existential), the predicate is `Decidable`
  (`decidablePackedReaches`), so the finite verification is a kernel `decide`.
* `reachesTerminalIn_toBlocks_of_packedReaches` — the **soundness bridge**:
  `packedReaches n k a → ReachesTerminalIn k (toBlocks n a)`. By induction on `k`: the base case is
  the packed↔`Matrix` terminal agreement (`isPackedTerminal_iff_isTerminalLayer`), and each
  inductive move decodes to a genuine `Matrix` move (`packedNeighbors_sound`) whose target reaches
  terminal in `k - 1` by the induction hypothesis. This is the direction the terminal chunk consumes
  to turn `∀ a ∈ spEnum, packedReaches 2 3 a` (a kernel `decide`) into `∀ g ∈ Sp(4, 𝔽₂),
  ReachesTerminalIn 3 g` (`LocalReduction 2 3`).

Only the block *decode* `toBlocks n a` is read (never a range hypothesis on `a`), so soundness holds
for every `a : ℕ`; the finite reachability check applies it at `n = 2` (`Sp(4, 𝔽₂)`) and `n = 1`
(`Sp(2, 𝔽₂)`).
-/

open Matrix

namespace CliffordCSS.Packed

/-! ### Packed bounded reachability -/

/-- **Packed bounded reachability** `packedReaches n k a`: the packed `2n × 2n` block `a` reaches a
terminal block in **at most `k` packed moves**. Defined by structural recursion on `k`, mirroring
the `Matrix`-level `ReachesTerminalIn` clause for clause:

* `k = 0` — `a` is already terminal (`IsPackedTerminal n a`);
* `k + 1` — `a` is terminal, or some one-move neighbour `a' ∈ packedNeighbors n a` reaches a
  terminal block in at most `k` moves.

Since `packedNeighbors n a` is a finite `List ℕ`, the `∃ a' ∈ …` is a bounded (decidable) search, so
the whole predicate is `Decidable` (`decidablePackedReaches`) and the finite verification is a
kernel `decide`. Proved to imply the `Matrix` predicate on the decode by
`reachesTerminalIn_toBlocks_of_packedReaches`. -/
def packedReaches (n : ℕ) : ℕ → ℕ → Prop
  | 0, a => IsPackedTerminal n a
  | (k + 1), a => IsPackedTerminal n a ∨ ∃ a' ∈ packedNeighbors n a, packedReaches n k a'


/-- Recursive case of `packedReaches` (definitional): reaching a terminal block in at most `k + 1`
moves is being terminal, or having a one-move neighbour that reaches one in at most `k` moves. The
packed analogue of `reachesTerminalIn_succ`. -/
@[simp] theorem packedReaches_succ (n k a : ℕ) :
    packedReaches n (k + 1) a ↔
      IsPackedTerminal n a ∨ ∃ a' ∈ packedNeighbors n a, packedReaches n k a' := Iff.rfl

/-- `packedReaches n k a` is **decidable**: at `k = 0` it is the decidable packed terminal test
(`decidableIsPackedTerminal`); at `k + 1` it is a disjunction whose second alternative is a bounded
existential over the finite list `packedNeighbors n a` (decidable given the induction hypothesis as
a `DecidablePred` for depth `k`). This is what makes the finite reachability verification a kernel
`decide`. -/
instance decidablePackedReaches (n k a : ℕ) : Decidable (packedReaches n k a) := by
  induction k generalizing a with
  | zero => exact decidableIsPackedTerminal n a
  | succ k ih =>
      letI : DecidablePred (packedReaches n k) := ih
      exact decidable_of_iff _ (packedReaches_succ n k a).symm

/-- **Soundness of packed bounded reachability**:
`packedReaches n k a → ReachesTerminalIn k (toBlocks n a)`. By induction on `k`.

* Base (`k = 0`): `packedReaches n 0 a` is `IsPackedTerminal n a`, which the packed↔`Matrix`
  terminal agreement `isPackedTerminal_iff_isTerminalLayer` turns into
  `IsTerminalLayer (toBlocks n a) = ReachesTerminalIn 0 (toBlocks n a)`.
* Step (`k + 1`): if `a` is terminal, same agreement gives `Or.inl`. Otherwise a neighbour
  `a' ∈ packedNeighbors n a` reaches terminal in `k` packed moves; `packedNeighbors_sound` decodes
  the packed edge to a genuine `Matrix` move `IsBlockMove (toBlocks n a) (toBlocks n a')`, and the
  induction hypothesis gives `ReachesTerminalIn k (toBlocks n a')`, so `Or.inr` with witness
  `toBlocks n a'`.

Size-generic (all `n`, all `a`); the direction the terminal chunk consumes to lift the kernel
`decide ∀ a ∈ spEnum, packedReaches 2 3 a` to `LocalReduction 2 3`. -/
theorem reachesTerminalIn_toBlocks_of_packedReaches {n : ℕ} (k a : ℕ)
    (h : packedReaches n k a) : ReachesTerminalIn k (toBlocks n a) := by
  induction k generalizing a with
  | zero => exact (isPackedTerminal_iff_isTerminalLayer n a).mp h
  | succ k ih =>
      rw [packedReaches_succ] at h
      rcases h with hterm | ⟨a', hmem, hreach⟩
      · exact Or.inl ((isPackedTerminal_iff_isTerminalLayer n a).mp hterm)
      · exact Or.inr ⟨toBlocks n a', packedNeighbors_sound hmem, ih a' hreach⟩

/-! ### Kernel-tractability guards

These `decide` checks exercise the packed bounded reachability natively at the two block widths the
finite verification `lem-local` runs over, confirming it evaluates in the kernel and giving the
per-expansion cost signal the terminal chunk's `∀ a ∈ spEnum, packedReaches 2 3 a` search needs (no
function-type closures materialised; no `native_decide`). -/

end CliffordCSS.Packed

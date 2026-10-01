# CliffordCSS

The structure of depth-one Clifford circuits for CSS codes, formalised in Lean 4: Appendix D of
*Beyond transversality: structure of Clifford circuits for CSS codes*,
[arXiv:2608.05688](https://arxiv.org/abs/2608.05688).

The headline is **Theorem D.1**, Eq. (D3) — `N_M = ⟨ S^Z_M, S^X_M, L_M ⟩`:

```lean
theorem fixedMatchingSlice_eq_sup_familyM (hσ : Function.Involutive σ) :
    fixedMatchingSlice C_X C_Z σ hσ
      = shearZFamilyM C_X C_Z σ hσ ⊔ shearXFamilyM C_X C_Z σ hσ ⊔ leviFamilyM C_X C_Z σ hσ
```

at the paper's full generality: an arbitrary finite qubit index type, arbitrary 𝔽₂-subspaces
`C_X`, `C_Z` with no orthogonality assumed, and an arbitrary matching — any involution `σ`. The
only hypothesis is that `σ` is an involution, i.e. that `M` is a matching at all.

Alongside it are Corollary D.2 (Eq. D4) and the six supporting lemmas D.3–D.8.

Nothing is assumed. Both headline theorems reduce to Lean's three standard axioms:

```
'CliffordCSS.fixedMatchingSlice_eq_sup_familyM' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

no `sorry`, no declared `axiom`, and no `native_decide` — the finite check behind Lemma D.4 is
re-run by the Lean kernel on every build.

## Scope

This is 𝔽₂ symplectic linear algebra throughout. Theorem D.1 is a group-theoretic identity in
`Sp(2n, 𝔽₂)`, matching the paper's own remark that Appendix D is "a statement about split subspaces
and nothing more". The quantum reading — that `Sp(2n, 𝔽₂)` is the Clifford group modulo Paulis,
that `(C_X, C_Z)` presents a CSS code, that the three families are depth-one physical gates — is
supplied by the paper, not by the Lean.

## Layout

| | |
|---|---|
| `CliffordCSS/DepthOne/` | Appendix D: the code-preserving group, the matching slice, the generating families, and the proof. `Theorem.lean` and `Corollary.lean` carry the headline results |
| `CliffordCSS/Symplectic/` | `Sp(2n, 𝔽₂)`, check matrices, and the symplectic action of Clifford circuits |
| `CliffordCSS/Packed/` | a `Nat`-bitmask representation of 𝔽₂ matrices, on which the kernel decision procedures run |
| `CliffordCSS/Pauli/`, `Normalizer/`, `Encoding/`, `Gates/` | Pauli strings, the Clifford normaliser sweep, stabiliser encoding circuits, and the concrete gate matrices |
| `CliffordCSS/ToMathlib/` | five results that belong upstream, under their upstream-relative paths |

## Building

```
ulimit -n 10240      # macOS defaults to 256, which leantar exhausts while unpacking
lake exe cache get
lake build
```

Mathlib is an ordinary dependency, pinned in `lake-manifest.json` to `e560e3ad`, so `cache get`
fetches it rather than building it — about 8,250 files.

Raise the file-descriptor limit first. `leantar` opens many archives at once, and on macOS's
default soft limit of 256 the download succeeds but unpacking fails en masse with
`Too many open files (os error 24)`. Nothing is lost when that happens: the archives are already
in `~/.cache/mathlib`, so re-running `lake exe cache get` after `ulimit -n` unpacks them without
downloading again. `sysctl kern.maxfilesperproc` gives the ceiling if 10240 is refused.

Two modules are genuine in-kernel decision procedures rather than ordinary elaboration, and they
dominate both time and memory. `Packed/CliffordCompleteness.lean` saturates the 720 packed elements
of `Sp(4, 𝔽₂)` under the Clifford generators (~2 min, ~7.4 GB). `DepthOne/LocalReductionTwo.lean`
decides bounded reverse reachability over that set, and is the more demanding of the two.
**Build on a machine with at least 32 GB of RAM**; 16 GB is not enough.

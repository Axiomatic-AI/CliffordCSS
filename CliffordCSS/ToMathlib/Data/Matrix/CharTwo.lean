/-
Copyright (c) 2026 Frank Koppens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frank Koppens
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Matrices over a ring of characteristic two

Entrywise consequences of `CharP R 2` for matrices over `R`.

## Main results

* `Matrix.add_self_eq_zero`: `M + M = 0` for a matrix over a semiring of characteristic two.
  Unlike `CharTwo.add_self_eq_zero` applied to the matrix ring, this needs neither a square shape
  nor `Fintype`/`DecidableEq`/`Nonempty` on the index types.
-/

public section

namespace Matrix

variable {m n R : Type*}

/-- **Every matrix over a ring of characteristic two is its own additive inverse**: `M + M = 0`,
entrywise `CharTwo.add_self_eq_zero`. Stated for a rectangular matrix over an arbitrary semiring of
characteristic two, so it applies where the matrix ring itself carries no `CharP` instance. -/
theorem add_self_eq_zero [Semiring R] [CharP R 2] (M : Matrix m n R) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (M i j)

end Matrix

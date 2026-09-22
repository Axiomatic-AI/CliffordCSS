/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The dimension of a matrix algebra

An addition to `Mathlib`, kept here rather than in the fork so that `Mathlib/` stays upstream.

## Main results

* `Matrix.finrank_eq_card_sq`: `Module.finrank 𝕜 (Matrix n n 𝕜) = (Fintype.card n) ^ 2`.
-/

@[expose] public section

namespace Matrix

variable {𝕜 n : Type*} [Field 𝕜] [Fintype n]

/-- **Nielsen & Chuang, Exercise 2.39 (2).** If `V` is a Hilbert space of dimension `d`, then the
operator space `L_V` has dimension `d²`. In the matrix picture `L_V = Matrix n n 𝕜` with
`d = Fintype.card n`, so `Module.finrank 𝕜 (Matrix n n 𝕜) = (Fintype.card n) ^ 2`. -/
theorem finrank_eq_card_sq :
    Module.finrank 𝕜 (Matrix n n 𝕜) = Fintype.card n ^ 2 := by
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq]

end Matrix

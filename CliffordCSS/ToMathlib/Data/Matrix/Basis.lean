/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Winston Yin
-/
module

public import Mathlib.Data.Matrix.Basis

/-!
# `vecMul` by a single-entry matrix

An addition to `Mathlib.Data.Matrix.Basis`, kept here rather than in the fork so that `Mathlib/`
stays upstream. It is the `vecMul` companion of upstream's `Matrix.single_mulVec`.

## Main results

* `Matrix.vecMul_single`: `x ᵥ* single i j c = Function.update 0 j (x i * c)`.
-/

@[expose] public section

variable {m n α : Type*}

namespace Matrix

variable [DecidableEq m] [DecidableEq n]

/-- **Row-vector multiplication by a single-entry matrix.** `x ᵥ* single i j c` is supported at
`j`, where it takes the value `x i * c`; the `vecMul` companion of `Matrix.single_mulVec`. -/
theorem vecMul_single [NonUnitalNonAssocSemiring α] [Fintype m]
    (i : m) (j : n) (c : α) (x : m → α) :
    vecMul x (single i j c) = Function.update (0 : n → α) j (x i * c) := by
  ext j'
  simp only [vecMul, dotProduct, single, of_apply, mul_ite, mul_zero]
  rcases eq_or_ne j j' with rfl | h
  · simp
  simp [h, h.symm]

end Matrix

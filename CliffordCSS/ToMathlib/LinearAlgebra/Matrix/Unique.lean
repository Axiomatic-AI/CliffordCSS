/-
Copyright (c) 2024 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson, Winston Yin
-/
module

public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.Data.ZMod.Basic

/-!
# One by one matrices over `ZMod 2`

An addition to `Mathlib.LinearAlgebra.Matrix.Unique`, kept here rather than in the fork so that
`Mathlib/` stays upstream.

## Main results

* `Matrix.eq_zero_or_one_of_unique`: a one by one matrix over `ZMod 2` is either `0` or `1`.
-/

@[expose] public section

variable {n : Type*} [Unique n]

namespace Matrix

/-- **The one by one matrices over `ZMod 2` are exactly `0` and `1`**: such a matrix is determined
by its single entry (`uniqueEquiv`), and `ZMod 2 = {0, 1}`. -/
theorem eq_zero_or_one_of_unique [DecidableEq n] (M : Matrix n n (ZMod 2)) : M = 0 ∨ M = 1 :=
  ((by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (uniqueEquiv M)).imp
    (fun h => uniqueEquiv.injective (by simpa using h))
    (fun h => uniqueEquiv.injective (by simpa using h))

end Matrix

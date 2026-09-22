/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# The exponential of a scalar multiple of an involution

Let `𝔸` be a normed `ℂ`-algebra and `a : 𝔸` an element with `a * a = 1` (an *involution*,
e.g. a Pauli matrix, a reflection, or any square root of `1`). This file gives the closed form of
its complex exponential:

`NormedSpace.exp (z • a) = Complex.cosh z • 1 + Complex.sinh z • a`.

The proof is the even/odd split of the exponential power series: `(z • a) ^ n = zⁿ • aⁿ` with
`aⁿ = 1` for even `n` and `aⁿ = a` for odd `n`, so the even terms sum (via `Complex.hasSum_cosh`)
to `cosh z • 1` and the odd terms (via `Complex.hasSum_sinh`) to `sinh z • a`. This is the abstract
core of the Euler-type "spin rotation" identity

`exp (i θ (n̂ · σ)) = cos θ · I + i sin θ · (n̂ · σ)`

(Nielsen & Chuang, Exercise 2.35). It mirrors `Quaternion.exp_of_re_eq_zero`, the analogous formula
for a purely imaginary quaternion (there `a * a = -1`, giving `cos`/`sin`).

The companion `NormedSpace.exp_smul_of_mul_self_eq_self` treats the neighbouring special case of an
*idempotent* `a` (`a * a = a`, e.g. a projector), where the even/odd split collapses to a single
term: `exp (z • a) = 1 + (Complex.exp z - 1) • a`.

## Main results

* `NormedSpace.exp_smul_of_mul_self_eq_one`: the closed form when `a * a = 1`.
* `NormedSpace.exp_smul_mul_I_of_mul_self_eq_one`: its real-angle trigonometric form
  `exp ((x * i) • a) = cos x • 1 + (sin x * i) • a` (Nielsen & Chuang, Exercise 4.2, eq. 4.7).
* `NormedSpace.smul_one_add_smul_mul_of_mul_self_eq_one`: the multiplication table of the span of
  `1` and an involution, `(a•1 + b•g)(d•1 + e•g) = (ad+be)•1 + (ae+bd)•g`, which computes products
  and squares of the normal forms above.
* `NormedSpace.exp_smul_of_mul_self_eq_self`: the closed form when `a * a = a` (idempotent),
  `exp (z • a) = 1 + (Complex.exp z - 1) • a`.
-/

@[expose] public section

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]

/-- **Euler's formula for an involution.** If `a` satisfies `a * a = 1` in a normed `ℂ`-algebra,
then for any `z : ℂ`,
`exp (z • a) = Complex.cosh z • 1 + Complex.sinh z • a`.

The exponential series `∑ₙ (n!)⁻¹ • (z • a) ^ n` splits by parity: since `(z • a) ^ n = zⁿ • aⁿ` and
`aⁿ` is `1` for even `n` and `a` for odd `n`, the even part is `(∑ₖ z^(2k)/(2k)!) • 1 = cosh z • 1`
and the odd part is `(∑ₖ z^(2k+1)/(2k+1)!) • a = sinh z • a`. Specialising `z` to `θ * I` and using
`Complex.cosh_mul_I`/`Complex.sinh_mul_I` recovers the trigonometric "rotation" form. -/
theorem exp_smul_of_mul_self_eq_one {a : 𝔸} (ha : a * a = 1) (z : ℂ) :
    exp (z • a) = Complex.cosh z • (1 : 𝔸) + Complex.sinh z • a := by
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact ha
  have hpe : ∀ k : ℕ, a ^ (2 * k) = 1 := fun k => by rw [pow_mul, ha2, one_pow]
  have hpo : ∀ k : ℕ, a ^ (2 * k + 1) = a := fun k => by rw [pow_succ, hpe k, one_mul]
  rw [exp_eq_tsum ℂ]
  refine HasSum.tsum_eq ?_
  refine HasSum.even_add_odd ?_ ?_
  · -- even terms: `(2k)!⁻¹ • (z • a) ^ (2k) = (z^(2k)/(2k)!) • 1`, summing to `cosh z • 1`
    have h : (fun k : ℕ => (↑(2 * k).factorial : ℂ)⁻¹ • (z • a) ^ (2 * k))
        = (fun k : ℕ => (z ^ (2 * k) / ↑(2 * k).factorial) • (1 : 𝔸)) := by
      funext k; rw [smul_pow, hpe k, smul_smul, div_eq_mul_inv, mul_comm]
    rw [h]; exact (Complex.hasSum_cosh z).smul_const (1 : 𝔸)
  · -- odd terms: `(2k+1)!⁻¹ • (z • a) ^ (2k+1) = (z^(2k+1)/(2k+1)!) • a`, summing to `sinh z • a`
    have h : (fun k : ℕ => (↑(2 * k + 1).factorial : ℂ)⁻¹ • (z • a) ^ (2 * k + 1))
        = (fun k : ℕ => (z ^ (2 * k + 1) / ↑(2 * k + 1).factorial) • a) := by
      funext k; rw [smul_pow, hpo k, smul_smul, div_eq_mul_inv, mul_comm]
    rw [h]; exact (Complex.hasSum_sinh z).smul_const a

/-- **Nielsen & Chuang, Exercise 4.2, equation (4.7).** For an involution `a` (`a * a = 1`) in a
normed `ℂ`-algebra and a *real* number `x`,
`exp ((x * i) • a) = cos x • 1 + (sin x * i) • a`,
that is, `exp (i x a) = cos x · 1 + i sin x · a`.

This is the real-angle trigonometric specialisation of `exp_smul_of_mul_self_eq_one`: writing the
exponent as `z • a` with `z = x * i`, `Complex.cosh_mul_I` turns `cosh z` into `cos x` and
`Complex.sinh_mul_I` turns `sinh z` into `sin x * i`. Specialising further to `a = X, Y, Z` (a Pauli
matrix) with `x = -θ/2` gives Nielsen & Chuang's rotation operators `R_x, R_y, R_z = exp(-iθσ/2)`
(equations 4.4–4.6). -/
theorem exp_smul_mul_I_of_mul_self_eq_one {a : 𝔸} (ha : a * a = 1) (x : ℝ) :
    exp (((x : ℂ) * Complex.I) • a)
      = (Real.cos x : ℂ) • (1 : 𝔸) + ((Real.sin x : ℂ) * Complex.I) • a := by
  rw [exp_smul_of_mul_self_eq_one ha, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **Product law for the span of `1` and an involution.** If `g` satisfies `g * g = 1` in a
`ℂ`-algebra `A`, the `ℂ`-linear span of `1` and `g` is closed under multiplication:
`(a • 1 + b • g) * (d • 1 + e • g) = (a * d + b * e) • 1 + (a * e + b * d) • g`.

This is the multiplication table of the two-dimensional algebra `ℂ[g]/(g² - 1)`. Applied to the
`cos x • 1 ± (sin x * i) • g` normal forms of `exp (±(x * i) • g)`
(`exp_smul_mul_I_of_mul_self_eq_one`), it computes their products and squares — e.g. the square
`(exp ((x * i) • g))² = exp ((2 x * i) • g)` in `cos`/`sin` form via the double-angle identities. -/
theorem smul_one_add_smul_mul_of_mul_self_eq_one {A : Type*} [Ring A] [Algebra ℂ A] {g : A}
    (hg : g * g = 1) (a b d e : ℂ) :
    (a • (1 : A) + b • g) * (d • 1 + e • g)
      = (a * d + b * e) • (1 : A) + (a * e + b * d) • g := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hg]
  module

/-- **Euler's formula for an idempotent.** If `a` satisfies `a * a = a` in a normed `ℂ`-algebra
(e.g. `a` is a projector `P = P²`), then for any `z : ℂ`,
`exp (z • a) = 1 + (Complex.exp z - 1) • a`.

The exponential series `∑ₙ (n!)⁻¹ • (z • a) ^ n` has `(z • a) ^ n = zⁿ • aⁿ` with `aⁿ = a` for every
`n ≥ 1` and `a⁰ = 1`. Thus the `n = 0` term contributes `1` and the tail `∑_{n≥1} (zⁿ/n!) • a` sums
to `(Complex.exp z - 1) • a`, since `∑_{n≥1} zⁿ/n! = Complex.exp z - 1`. This is the idempotent
counterpart of `exp_smul_of_mul_self_eq_one`; for a rank-one projector `P = |ψ⟩⟨ψ|` and `z = -iΔt`
it gives the projector-Hamiltonian propagator `exp(-i|ψ⟩⟨ψ|Δt) = I + (e^{-iΔt} - 1)|ψ⟩⟨ψ|`
(Nielsen & Chuang, §6.2, the Hamiltonian `|x⟩⟨x|` simulated in Exercise 6.7). -/
theorem exp_smul_of_mul_self_eq_self {a : 𝔸} (ha : a * a = a) (z : ℂ) :
    exp (z • a) = (1 : 𝔸) + (Complex.exp z - 1) • a := by
  -- `aⁿ = a` for `n ≥ 1` (and `a⁰ = 1`).
  have hpow : ∀ n : ℕ, a ^ (n + 1) = a := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, ha]
  -- Rewrite the `n`-th series term as `(zⁿ/n!) • a` plus a correction `1 - a` supported at `n = 0`.
  have key : (fun n : ℕ => (↑n.factorial : ℂ)⁻¹ • (z • a) ^ n)
      = fun n : ℕ => (z ^ n / ↑n.factorial) • a + (if n = 0 then ((1 : 𝔸) - a) else 0) := by
    funext n
    cases n with
    | zero => simp
    | succ m =>
        rw [smul_pow, hpow m, smul_smul, div_eq_mul_inv, mul_comm,
          if_neg (Nat.succ_ne_zero m), add_zero]
  -- The `(zⁿ/n!) • a` part sums to `(Complex.exp z) • a`; the correction sums to `1 - a`.
  have h1 : HasSum (fun n : ℕ => (z ^ n / ↑n.factorial) • a) (Complex.exp z • a) := by
    have hs : HasSum (fun n : ℕ => z ^ n / ↑n.factorial) (Complex.exp z) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact expSeries_div_hasSum_exp z
    exact hs.smul_const a
  have h2 : HasSum (fun n : ℕ => if n = 0 then ((1 : 𝔸) - a) else 0) ((1 : 𝔸) - a) :=
    hasSum_ite_eq 0 ((1 : 𝔸) - a)
  rw [exp_eq_tsum ℂ]
  refine HasSum.tsum_eq ?_
  rw [key]
  have hsum := h1.add h2
  convert hsum using 1
  rw [sub_smul, one_smul]
  abel

end NormedSpace

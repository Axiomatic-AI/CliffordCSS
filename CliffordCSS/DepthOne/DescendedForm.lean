import CliffordCSS.DepthOne.LogicalSpace
import CliffordCSS.Symplectic.FirstPair
import CliffordCSS.Symplectic.Residual
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The logical space `𝒞^⊥ / 𝒞` and its descended symplectic form
(Beyond transversality, App. D / setup)

Pure mathematics : the **logical space** of *Beyond transversality*
(arXiv:2608.05688) together with the symplectic form it carries. The paper's **Corollary**
(*Depth-one logical generation*, `cor-depthone`, App. D) is stated over the logical action
`λ : N_full ↠ Sp(2k)`; for `λ` to be defined the CSS label space `𝒞` must be **isotropic**, so that
`𝒞 ⊆ 𝒞^⊥` and the quotient `𝒞^⊥ / 𝒞` — the **logical space** — makes sense. On that quotient the
phase-space symplectic form **descends** to a symplectic form; the codomain of `λ` is the symplectic
group of this quotient. This file builds the quotient and the descended form; the logical action `λ`
itself is Part 3.

## The load-bearing construction (there is no Mathlib lemma for it)

Mathlib provides no lemma descending a bilinear form to a quotient (three independent meaning
searches, re-run 2026-08-14, return only nondegeneracy criteria — `LinearMap.BilinForm.orthogonal`,
`nondegenerate_iff_ker_eq_bot`, `orthogonal_orthogonal` — never a construction of the induced form).
So the descent is **built by hand**. A bilinear form is a linear-map-into-a-linear-map, so the
descent is `Submodule.liftQ` applied **twice**, well-definedness on each side supplied by the fact
that the symplectic form vanishes on `𝒞^⊥ × 𝒞` and on `𝒞 × 𝒞^⊥`
(`symplecticForm_eq_zero_of_mem_of_mem_perp`) — which needs only membership in `𝒞^⊥`, *not* isotropy
of `𝒞`. Consequently the descended form is well-defined for **any** subspace `L`, and its
nondegeneracy holds for any `L` too (via the double-orthogonal `(L^⊥)^⊥ = L`); isotropy `𝒞 ⊆ 𝒞^⊥`
is what makes the *quotient* the paper's logical space, and enters only in the dimension count
(`= 2k`, a later chunk) and in `λ`.

## What is defined and proved

* `codeInPerp L`, `logicalSpace L` — the submodule `L` viewed inside `↥L^⊥` and the quotient
  `logicalSpace L = ↥L^⊥ ⧸ codeInPerp L`, i.e. `𝒞^⊥ / 𝒞` (the idiomatic subtype-quotient shape).
* `perpRestrict L` — `symplecticBilin` restricted to `↥L^⊥` (via `LinearMap.compl₁₂`), with
  `perpRestrict_apply`.
* `logicalBilin L` — **the descended symplectic form** on `logicalSpace L`, built by the double
  `Submodule.liftQ`, with the descent identity `logicalBilin_mk`
  (`logicalBilin L ⟦x⟧ ⟦y⟧ = symplecticForm x y`).
* `logicalBilin_comm` / `logicalBilin_isSymm`, `logicalBilin_self` / `logicalBilin_isAlt` — the
  descended form is **symmetric** and **alternating** (it inherits both from `symplecticForm`).
* `symplecticPerp_eq_orthogonal`, `symplecticBilin_nondegenerate`, `symplecticPerp_symplecticPerp`
  (`(L^⊥)^⊥ = L`) — the ambient facts, then `logicalBilin_nondegenerate` — **the descended form is
  nondegenerate**, so `𝒞^⊥ / 𝒞` is a genuine symplectic space.

`native_decide` is not used; no `sorry`, no new `axiom`. All of Appendix D is `𝔽₂`-symplectic linear
algebra naming the raw carrier `Matrix`/`ZMod`/`Submodule`. -/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The label space `L` viewed as a subspace of `↥L^⊥` (the preimage of `L` under the inclusion
`L^⊥ ↪ V`). For the CSS label space this is `𝒞` sitting inside `𝒞^⊥`; it is the submodule the
logical space `logicalSpace L = ↥L^⊥ ⧸ codeInPerp L` quotients by. -/
noncomputable def codeInPerp (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) :
    Submodule (ZMod 2) ↥(symplecticPerp L) :=
  L.comap (symplecticPerp L).subtype

/-- The **logical space** `L^⊥ / L` of *Beyond transversality* — for the CSS label space `𝒞` (when
isotropic, `𝒞 ⊆ 𝒞^⊥`) this is `𝒞^⊥ / 𝒞`, the space the logical action `λ` acts on. Realized as the
quotient of the subtype `↥L^⊥` by `codeInPerp L`, the idiomatic subtype-quotient shape. -/
abbrev logicalSpace (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) : Type _ :=
  ↥(symplecticPerp L) ⧸ codeInPerp L

/-- **The symplectic form vanishes on `L × L^⊥`.** If `w ∈ L` and `x ∈ L^⊥` then
`⟨w, x⟩ = symplecticForm w x = 0`. This is the defining property of the symplectic complement
(`mem_symplecticPerp`); it — and its `comm`-flipped partner — is the well-definedness input for the
two `Submodule.liftQ`s that build the descended form. Note it uses only `x ∈ L^⊥`, never isotropy of
`L`. -/
theorem symplecticForm_eq_zero_of_mem_of_mem_perp {L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)}
    {w x : ι ⊕ ι → ZMod 2} (hw : w ∈ L) (hx : x ∈ symplecticPerp L) :
    symplecticForm w x = 0 :=
  (mem_symplecticPerp.mp hx) w hw

/-- The symplectic form **restricted to `↥L^⊥`**, as a bundled bilinear form on the subtype: it
computes `symplecticForm` on the underlying vectors (`perpRestrict_apply`). Built with
`LinearMap.compl₁₂` from the two inclusions `L^⊥ ↪ V`; this is the form that then descends through
the quotient by `codeInPerp L`. -/
noncomputable def perpRestrict (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) ↥(symplecticPerp L) :=
  symplecticBilin.compl₁₂ (symplecticPerp L).subtype (symplecticPerp L).subtype

@[simp] theorem perpRestrict_apply (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2))
    (w x : ↥(symplecticPerp L)) :
    perpRestrict L w x = symplecticForm (w : ι ⊕ ι → ZMod 2) (x : ι ⊕ ι → ZMod 2) := by
  simp only [perpRestrict, LinearMap.compl₁₂_apply, Submodule.coe_subtype, symplecticBilin_apply]

/-- **The descended symplectic form** on the logical space `L^⊥ / L`. Built by applying
`Submodule.liftQ` twice to `perpRestrict L`: the first descends the left argument (well-defined
because `perpRestrict L w = 0` when `w ∈ L`, since then `⟨w, ·⟩` vanishes on `L^⊥`), and after a
`flip` the second descends the right argument (dually). The descent identity is `logicalBilin_mk`:
`logicalBilin L ⟦x⟧ ⟦y⟧ = symplecticForm x y`. This is the object the paper's `Sp(2k)` is the
symplectic group of. -/
noncomputable def logicalBilin (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) (logicalSpace L) :=
  (codeInPerp L).liftQ
    (((codeInPerp L).liftQ (perpRestrict L) (by
        intro w hw
        rw [LinearMap.mem_ker]
        ext x
        simp only [perpRestrict_apply, LinearMap.zero_apply]
        exact symplecticForm_eq_zero_of_mem_of_mem_perp (Submodule.mem_comap.mp hw) x.2)).flip)
    (by
      intro y hy
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun q => ?_
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (codeInPerp L) q
      simp only [LinearMap.flip_apply, Submodule.liftQ_apply, perpRestrict_apply,
        LinearMap.zero_apply]
      rw [symplecticForm_comm]
      exact symplecticForm_eq_zero_of_mem_of_mem_perp (Submodule.mem_comap.mp hy) w.2)

/-- **The descent identity**: on representatives, the descended form is the phase-space symplectic
form. `logicalBilin L ⟦x⟧ ⟦y⟧ = symplecticForm x y` for `x, y ∈ L^⊥`. -/
@[simp] theorem logicalBilin_mk (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2))
    (x y : ↥(symplecticPerp L)) :
    logicalBilin L (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
      = symplecticForm (x : ι ⊕ ι → ZMod 2) (y : ι ⊕ ι → ZMod 2) := by
  simp only [logicalBilin, Submodule.liftQ_apply, LinearMap.flip_apply, perpRestrict_apply]
  exact symplecticForm_comm _ _


/-- **Bridge to Mathlib's orthogonal-complement API**: the symplectic complement `symplecticPerp L`
(defined via `Submodule.orthogonalBilin`) is the same as `LinearMap.BilinForm.orthogonal
symplecticBilin L`. This lets the double-orthogonal lemma `orthogonal_orthogonal` apply to
`symplecticPerp`. -/
theorem symplecticPerp_eq_orthogonal (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) :
    symplecticPerp L = symplecticBilin.orthogonal L := by
  ext v
  rw [mem_symplecticPerp, LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [LinearMap.BilinForm.isOrtho_def, symplecticBilin_apply]

/-- The ambient symplectic form is **left-separating**: if `⟨x, y⟩ = 0` for all `y` then `x = 0`.
Proved by testing on the coordinate vectors `Pi.single (inr a) 1` and `Pi.single (inl a) 1`, whose
pairing with `x` reads off the components `x (inl a)` and `x (inr a)`
(`symplecticForm_single_inr` / `symplecticForm_single_inl`). -/
theorem symplecticBilin_separatingLeft : (symplecticBilin (ι := ι)).SeparatingLeft := by
  intro x hx
  have hxy : ∀ y, symplecticForm x y = 0 := fun y => by
    have := hx y; rwa [symplecticBilin_apply] at this
  funext i
  cases i with
  | inl a =>
      have h := hxy (Pi.single (Sum.inr a) 1)
      rw [symplecticForm_comm, symplecticForm_single_inr] at h
      simpa using h
  | inr a =>
      have h := hxy (Pi.single (Sum.inl a) 1)
      rw [symplecticForm_comm, symplecticForm_single_inl] at h
      simpa using h

/-- The ambient symplectic form is **nondegenerate**. Left-separation is
`symplecticBilin_separatingLeft`; right-separation follows from it by symmetry
(`symplecticForm_comm`). -/
theorem symplecticBilin_nondegenerate : (symplecticBilin (ι := ι)).Nondegenerate :=
  ⟨symplecticBilin_separatingLeft, fun y hy =>
    symplecticBilin_separatingLeft y fun x => by
      have := hy x
      rwa [symplecticBilin_apply, symplecticForm_comm, ← symplecticBilin_apply] at this⟩


end CliffordCSS

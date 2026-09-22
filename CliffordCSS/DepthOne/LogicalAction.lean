import CliffordCSS.DepthOne.DescendedForm
import CliffordCSS.DepthOne.CodePreserving
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The logical action `λ : N_full → Sp(2k)` (Beyond transversality, App. D / general)

Pure mathematics : the **logical action** of *Beyond transversality*
(arXiv:2608.05688). The paper's **Corollary** (*Depth-one logical generation*, `cor-depthone`,
App. D) is stated over the homomorphism `λ : N_full ↠ Sp(2k)` (`app_general.tex`,
Eq. `general-lact`): every code-preserving `g ∈ N_full = Stab_{Sp(2n)}(𝒞)` preserves `𝒞`, hence
`𝒞^⊥`, hence induces an action on the quotient `𝒞^⊥ / 𝒞` — the logical space — and this assignment
is a group homomorphism into the symplectic group of that quotient. This file builds `λ`, completing
the machinery the Corollary is stated over.

## The action and the covariance convention

The paper's phase-space action is on **row vectors from the right**, `v ↦ v ᵥ* G`
(`app_general.tex`: *"Vectors are rows and matrices act on the right"*). The induced map on the
quotient, `logicalEnd G : ⟦v⟧ ↦ ⟦v ᵥ* G⟧`, is therefore an *anti*-homomorphism into the linear
automorphism group `𝒞^⊥/𝒞 ≃ₗ 𝒞^⊥/𝒞` (whose product is function composition,
`LinearEquiv.mul_apply`): `logicalEnd (G * H) = logicalEnd H ∘ logicalEnd G`. The paper's
`λ : N_full → Sp(2k)` is a genuine *homomorphism*; in the abstract-quotient presentation (design
decision `twofoldD1:dec-w7-lambda-abstract-quotient` — avoid choosing a symplectic basis, so the
codomain is the automorphism group of the abstract quotient, not a matrix group) this is realized
by the **standard right-action-to-representation via the inverse**, `λ(G) := ⟦v⟧ ↦ ⟦v ᵥ* G⁻¹⟧`.
Because `N_full` is a group, `{λ(G) : G ∈ N_full}` equals `{logicalEnd G : G ∈ N_full}` as a set, so
the image subgroup — all the Corollary's generation equation `λ(N_dep) = ⟨⋃_M λ(…)⟩` refers to — is
independent of the convention. `logicalEnd` (the raw `⟦v⟧ ↦ ⟦v ᵥ* G⟧`) is kept public for
transparency; `logicalAction` is the genuine homomorphism.

## What is defined and proved

* `vecMul_mem_symplecticPerp` — a code-preserving `G` maps `𝒞^⊥` into itself (`G` symplectic +
  `G` preserves `𝒞` setwise, no isotropy needed).
* `perpVecMul G` — the right action `v ↦ v ᵥ* G` restricted to an endomorphism of `↥𝒞^⊥`, with
  `perpVecMul_coe`.
* `logicalEnd G` — the induced endomorphism `⟦v⟧ ↦ ⟦v ᵥ* G⟧` of the logical space `𝒞^⊥/𝒞`
  (`Submodule.mapQ`), with `logicalEnd_mk`.
* `logicalActionEnd` — the covariant assignment `G ↦ logicalEnd G⁻¹` as a **monoid homomorphism**
  into `Module.End`.
* `logicalSymplecticGroup 𝒞` — the paper's `Sp(2k)`: the subgroup of `𝒞^⊥/𝒞 ≃ₗ 𝒞^⊥/𝒞` of
  linear automorphisms preserving the descended symplectic form `logicalBilin`.
* `logicalAction` — `λ` as a **monoid homomorphism** `N_full → (𝒞^⊥/𝒞 ≃ₗ 𝒞^⊥/𝒞)`, with
  `logicalAction_mk`; `logicalAction_mem_logicalSymplecticGroup` (each `λ(G)` is an isometry of the
  descended form); and `logicalActionHom` — `λ` with codomain restricted to `logicalSymplecticGroup`
  (the paper's `Sp(2k)`). Surjectivity (the paper's `↠`) is **not** proved here: the Corollary needs
  only the homomorphism property, so surjectivity is deferred (and is not asserted).

All is `𝔽₂`-symplectic linear algebra naming the raw carrier `Matrix`/`ZMod`/`Submodule`. No
`sorry`, no new `axiom`, no `native_decide`. -/

open Matrix

namespace CliffordCSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {C_X C_Z : Submodule (ZMod 2) (ι → ZMod 2)}

/-- **A code-preserving `G` maps `𝒞^⊥` into itself.** If `G ∈ N_full` (symplectic and setwise
stabilizing `𝒞`) and `x ∈ 𝒞^⊥`, then `x ᵥ* G ∈ 𝒞^⊥`. For `w ∈ 𝒞`, the preimage `w ᵥ* G⁻¹` lies in
`𝒞` (as `G⁻¹` is code-preserving), and symplectic invariance of the form gives
`⟨w, x ᵥ* G⟩ = ⟨(w ᵥ* G⁻¹) ᵥ* G, x ᵥ* G⟩ = ⟨w ᵥ* G⁻¹, x⟩ = 0`. Uses only membership in `𝒞^⊥`, not
isotropy of `𝒞`. -/
theorem vecMul_mem_symplecticPerp {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ codePreservingGroup C_X C_Z) {x : ι ⊕ ι → ZMod 2}
    (hx : x ∈ symplecticPerp (cssLabelSpaceSum C_X C_Z)) :
    x ᵥ* (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) ∈ symplecticPerp (cssLabelSpaceSum C_X C_Z) := by
  rw [mem_symplecticPerp]
  intro w hw
  have hw' : w ᵥ* ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
      ∈ cssLabelSpaceSum C_X C_Z := (mem_codePreservingGroup_iff.mp (inv_mem hG) w).mp hw
  have hGG : ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))
      * (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  have hpres := mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mp G.2
    (w ᵥ* ((G⁻¹ : ↥(binarySymplecticGroup ι)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2))) x
  rw [Matrix.vecMul_vecMul, hGG, Matrix.vecMul_one] at hpres
  rw [hpres]
  exact symplecticForm_eq_zero_of_mem_of_mem_perp hw' hx

/-- The right action `v ↦ v ᵥ* G` of a code-preserving `G`, restricted to a linear endomorphism of
`↥𝒞^⊥` (well-defined by `vecMul_mem_symplecticPerp`). -/
noncomputable def perpVecMul {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ codePreservingGroup C_X C_Z) :
    ↥(symplecticPerp (cssLabelSpaceSum C_X C_Z)) →ₗ[ZMod 2]
      ↥(symplecticPerp (cssLabelSpaceSum C_X C_Z)) :=
  ((G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)).vecMulLinear).restrict
    (fun x hx => by rw [Matrix.vecMulLinear_apply]; exact vecMul_mem_symplecticPerp hG hx)

@[simp] theorem perpVecMul_coe {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ codePreservingGroup C_X C_Z) (x : ↥(symplecticPerp (cssLabelSpaceSum C_X C_Z))) :
    ((perpVecMul hG x : ↥(symplecticPerp (cssLabelSpaceSum C_X C_Z))) : ι ⊕ ι → ZMod 2)
      = (x : ι ⊕ ι → ZMod 2) ᵥ* (G : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2)) := by
  rw [perpVecMul, LinearMap.restrict_coe_apply, Matrix.vecMulLinear_apply]

/-- The endomorphism of the logical space `𝒞^⊥/𝒞` induced by the right action `⟦v⟧ ↦ ⟦v ᵥ* G⟧` of a
code-preserving `G`. Built with `Submodule.mapQ` from `perpVecMul G`; the quotient is well-defined
because `G` preserves `𝒞` setwise (`mem_codePreservingGroup_iff`), so `⟦v⟧ = 0 ⟹ ⟦v ᵥ* G⟧ = 0`. -/
noncomputable def logicalEnd {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ codePreservingGroup C_X C_Z) :
    Module.End (ZMod 2) (logicalSpace (cssLabelSpaceSum C_X C_Z)) :=
  Submodule.mapQ _ _ (perpVecMul hG) (by
    intro y hy
    rw [Submodule.mem_comap]
    simp only [codeInPerp, Submodule.mem_comap, Submodule.coe_subtype] at hy ⊢
    rw [perpVecMul_coe]
    exact (mem_codePreservingGroup_iff.mp hG _).mp hy)

@[simp] theorem logicalEnd_mk {G : ↥(binarySymplecticGroup ι)}
    (hG : G ∈ codePreservingGroup C_X C_Z)
    (x : ↥(symplecticPerp (cssLabelSpaceSum C_X C_Z))) :
    logicalEnd hG (Submodule.Quotient.mk x) = Submodule.Quotient.mk (perpVecMul hG x) := by
  rw [logicalEnd, Submodule.mapQ_apply]

/-- **The logical action as a monoid homomorphism into `Module.End`.** `G ↦ logicalEnd G⁻¹`: because
the right action `⟦v⟧ ↦ ⟦v ᵥ* G⟧` is an anti-homomorphism, the covariant homomorphism represents `G`
by the action of `G⁻¹` (standard right-action-to-representation). Multiplicativity is the identity
`(G * H)⁻¹ = H⁻¹ * G⁻¹` fed through `vecMul_vecMul`. -/
noncomputable def logicalActionEnd :
    ↥(codePreservingGroup C_X C_Z) →*
      Module.End (ZMod 2) (logicalSpace (cssLabelSpaceSum C_X C_Z)) where
  toFun G := logicalEnd (inv_mem G.2)
  map_one' := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [logicalEnd_mk]
    refine congrArg _ (Subtype.ext ?_)
    simp [perpVecMul_coe]
  map_mul' := by
    intro G H
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [Module.End.mul_apply, logicalEnd_mk, logicalEnd_mk, logicalEnd_mk]
    refine congrArg _ (Subtype.ext ?_)
    simp only [perpVecMul_coe]
    rw [Matrix.vecMul_vecMul]
    congr 1
    rw [Subgroup.coe_mul, _root_.mul_inv_rev, Submonoid.coe_mul]

@[simp] theorem logicalActionEnd_mk (G : ↥(codePreservingGroup C_X C_Z))
    (x : ↥(symplecticPerp (cssLabelSpaceSum C_X C_Z))) :
    logicalActionEnd G (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (perpVecMul (inv_mem G.2) x) :=
  logicalEnd_mk _ x

/-- **The logical symplectic group `Sp(2k)`**: the subgroup of linear automorphisms of the logical
space `𝒞^⊥/𝒞` preserving the descended symplectic form `logicalBilin`. This is the abstract-quotient
realization of the paper's codomain for `λ` (design decision
`twofoldD1:dec-w7-lambda-abstract-quotient`). -/
def logicalSymplecticGroup (L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)) :
    Subgroup (logicalSpace L ≃ₗ[ZMod 2] logicalSpace L) where
  carrier := {f | ∀ x y, logicalBilin L (f x) (f y) = logicalBilin L x y}
  one_mem' := fun x y => rfl
  mul_mem' {f g} hf hg := fun x y => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hf, hg]
  inv_mem' {f} hf := fun x y => by simpa using (hf (f⁻¹ x) (f⁻¹ y)).symm

/-- **The logical action `λ : N_full → Sp(2k)` as a monoid homomorphism** into the automorphism
group of the logical space `𝒞^⊥/𝒞`. Obtained from `logicalActionEnd` by lifting its (necessarily
invertible, since `N_full` is a group) images into the units of `Module.End`
(`MonoidHom.toHomUnits`) and identifying those units with linear automorphisms
(`generalLinearEquiv`). The computation `logicalAction_mk` shows `λ(G) ⟦v⟧ = ⟦v ᵥ* G⁻¹⟧`. -/
noncomputable def logicalAction :
    ↥(codePreservingGroup C_X C_Z) →*
      (logicalSpace (cssLabelSpaceSum C_X C_Z) ≃ₗ[ZMod 2]
        logicalSpace (cssLabelSpaceSum C_X C_Z)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (logicalSpace (cssLabelSpaceSum C_X C_Z))).toMonoidHom.comp logicalActionEnd.toHomUnits

theorem logicalAction_apply (G : ↥(codePreservingGroup C_X C_Z))
    (q : logicalSpace (cssLabelSpaceSum C_X C_Z)) :
    logicalAction G q = logicalActionEnd G q := rfl

@[simp] theorem logicalAction_mk (G : ↥(codePreservingGroup C_X C_Z))
    (x : ↥(symplecticPerp (cssLabelSpaceSum C_X C_Z))) :
    logicalAction G (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (perpVecMul (inv_mem G.2) x) := by
  rw [logicalAction_apply, logicalActionEnd_mk]

/-- **Each `λ(G)` is an isometry of the descended symplectic form**, so `λ` lands in the logical
symplectic group `Sp(2k)`. On representatives `λ(G) ⟦x⟧ = ⟦x ᵥ* G⁻¹⟧`, and `G⁻¹` is symplectic, so
`⟨x ᵥ* G⁻¹, y ᵥ* G⁻¹⟩ = ⟨x, y⟩`. -/
theorem logicalAction_mem_logicalSymplecticGroup (G : ↥(codePreservingGroup C_X C_Z)) :
    logicalAction G ∈ logicalSymplecticGroup (cssLabelSpaceSum C_X C_Z) := by
  intro q q'
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
  rw [logicalAction_mk, logicalAction_mk, logicalBilin_mk, logicalBilin_mk, perpVecMul_coe,
    perpVecMul_coe]
  exact mem_binarySymplecticGroup_iff_symplecticForm_vecMul.mp
    (G : ↥(binarySymplecticGroup ι))⁻¹.2 (x : ι ⊕ ι → ZMod 2) (y : ι ⊕ ι → ZMod 2)

/-- **The logical action `λ` with codomain the logical symplectic group `Sp(2k)`** — the paper's
`λ : N_full → Sp(2k)` as a monoid homomorphism into the symplectic group of `𝒞^⊥/𝒞`. This is the
single fact the Corollary consumes; surjectivity (`↠`) is not proved here. -/
noncomputable def logicalActionHom :
    ↥(codePreservingGroup C_X C_Z) →*
      ↥(logicalSymplecticGroup (cssLabelSpaceSum C_X C_Z)) :=
  logicalAction.codRestrict (logicalSymplecticGroup (cssLabelSpaceSum C_X C_Z)).toSubmonoid
    logicalAction_mem_logicalSymplecticGroup

/-- **The logical space has dimension `2k`.** Under isotropy `𝒞 ⊆ 𝒞^⊥` (the Corollary's standing
hypothesis), the symplectic complement `𝒞^⊥` has dimension `2n − dim 𝒞` (nondegeneracy,
`finrank_orthogonal`), and `𝒞` embeds as `codeInPerp 𝒞 ≅ 𝒞` inside `𝒞^⊥` (isotropy,
`comapSubtypeEquivOfLe`), so passing to the quotient drops another `dim 𝒞`. Hence the dimension
bookkeeping `dim (𝒞^⊥/𝒞) + 2·dim 𝒞 = 2n` — the paper's `r + 2k + r = 2n` (App. `general-decomp`,
with `r = dim 𝒞`), i.e. `dim (𝒞^⊥/𝒞) = 2(n − dim 𝒞) = 2k`. This is the one place isotropy enters
the dimension count. -/
theorem finrank_logicalSpace_add_two_mul {L : Submodule (ZMod 2) (ι ⊕ ι → ZMod 2)}
    (hL : IsIsotropic L) :
    Module.finrank (ZMod 2) (logicalSpace L) + 2 * Module.finrank (ZMod 2) ↥L
      = 2 * Fintype.card ι := by
  have hle : L ≤ symplecticPerp L := isIsotropic_iff_le_symplecticPerp.mp hL
  have e1 : Module.finrank (ZMod 2) (logicalSpace L)
      + Module.finrank (ZMod 2) ↥(codeInPerp L)
      = Module.finrank (ZMod 2) ↥(symplecticPerp L) :=
    Submodule.finrank_quotient_add_finrank (codeInPerp L)
  have e2 : Module.finrank (ZMod 2) ↥(codeInPerp L) = Module.finrank (ZMod 2) ↥L :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have e3 : Module.finrank (ZMod 2) ↥(symplecticPerp L)
      = Module.finrank (ZMod 2) (ι ⊕ ι → ZMod 2) - Module.finrank (ZMod 2) ↥L := by
    rw [symplecticPerp_eq_orthogonal]
    exact LinearMap.BilinForm.finrank_orthogonal symplecticBilin_nondegenerate L
  have hle2 : Module.finrank (ZMod 2) ↥L ≤ Module.finrank (ZMod 2) (ι ⊕ ι → ZMod 2) :=
    Submodule.finrank_le L
  have hV : Module.finrank (ZMod 2) (ι ⊕ ι → ZMod 2) = 2 * Fintype.card ι := by
    rw [Module.finrank_pi, Fintype.card_sum, two_mul]
  omega

end CliffordCSS

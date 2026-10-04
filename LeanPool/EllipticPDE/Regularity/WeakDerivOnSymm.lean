/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.WeakDerivUnique
public import LeanPool.EllipticPDE.Regularity.DifferentiatedEquation


/-!
# Mixed second weak derivatives commute

`EllipticPdes.Regularity.differentiated_weakForm_wkInfty` produces an equation whose principal
unknown is the vector `(∂_ℓ∂ᵢu)ᵢ`, one derivative in the differentiation direction of every
first derivative of the solution. The induction of Guo, *Partial Differential Equations* (Course
Lecture Notes), Theorem VIII.3.2 (p. 65) consumes it as an equation for `∂_ℓu`,
whose gradient is `(∂ᵢ∂_ℓu)ᵢ`. Those two vectors agree only because mixed weak derivatives
commute, and `HasIteratedWeakDerivOn` is deliberately built without presuming it.

## Absence of local integrability

Testing shows only that the difference of the two second derivatives annihilates every test
function supported in the region, and the fundamental lemma of the calculus of variations turns
that into vanishing almost everywhere on an open set. Reaching for it here would drag in local
integrability of an `L²` class, which is a detour.

A cutoff is shorter and is the form every consumer below takes anyway. For a test function `χ`
    supported in
the region, `χ·ρ` is admissible for every whole-space test function `ρ`, so the whole-space
class of `χ·w` annihilates every test class and
`EllipticPdes.Regularity.annihilates_of_forall_testCls` kills it outright. Every term the
induction rewrites has a factor of the middle cutoff or one of its derivatives, and the outer
cutoff of the tower is identically `1` on a neighbourhood of that support, so the cut-off
identity is all that is ever asked for.

## Main declarations

* `partialD_comm`: classical partial derivatives of a smooth function commute.
* `mulTest_eq_zero_of_forall_testFn`: a class annihilating every test function is killed by any
  cutoff supported in the region.
* `mulTest_weakDerivOn_unique`: two weak derivatives of one class agree after a cutoff.
* `mulTest_mixed_weakDeriv_comm`: the two mixed second weak derivatives agree after a cutoff.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Classical partial derivatives commute -/

/-- **Schwarz for `partialD`.** The `i`-th partial of the `ℓ`-th partial of a smooth function is
the `ℓ`-th partial of its `i`-th partial.

`partialD ℓ φ` is `fun y => fderiv ℝ φ y (eℓ)`, an application of a differentiable
map into continuous linear maps against a constant, so `fderiv_clm_apply` reads its derivative
off `fderiv ℝ (fderiv ℝ φ)` with the two arguments flipped. Symmetry of the second Fréchet
derivative then swaps them back. -/
theorem partialD_comm {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i ℓ : Fin d) : partialD i (partialD ℓ φ) = partialD ℓ (partialD i φ) := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  have hFd : Differentiable ℝ (fderiv ℝ φ) := hF.differentiable (by simp)
  -- Both partials are entries of the second Fréchet derivative.
  have hentry : ∀ (a b : Fin d) (x : EuclideanSpace ℝ (Fin d)),
      partialD a (partialD b φ) x
        = fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b x
    have hrw : partialD b φ = fun y => (fderiv ℝ φ y) (EuclideanSpace.single b 1) := rfl
    simp only [partialD, hrw]
    rw [fderiv_clm_apply (hFd x) (differentiableAt_const _)]
    simp [ContinuousLinearMap.flip_apply]
  funext x
  rw [hentry i ℓ x, hentry ℓ i x]
  refine (hφ.contDiffAt.isSymmSndFDerivAt ?_) _ _
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

/-! ### Vanishing of a class orthogonal to every test function -/

/-- **Test-annihilation kills the cut-off class.** If `w ∈ L²(V)` integrates to zero against
every test function supported in `V`, then `χ·w = 0` for any test function `χ` supported in
`V`.

For a whole-space test function `ρ`, the product `χ·ρ` is supported in `tsupport χ ⊆ V`, so it
is one of the functions the hypothesis covers. The whole-space extension of `χ·w` therefore
annihilates every test class, and `annihilates_of_forall_testCls` makes it zero. Extension by
zero preserves the norm, so `χ·w` itself is zero. -/
theorem mulTest_eq_zero_of_forall_testFn {V : Set (EuclideanSpace ℝ (Fin d))}
    (hVm : MeasurableSet V) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn V χ) {w : L2D V}
    (h : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x in V, (w x : ℝ) * φ x = 0) :
    mulTest hχ w = 0 := by
  have hext : extendL2 hVm (mulTest hχ w) = 0 := by
    refine annihilates_of_forall_testCls (fun ρ hρcd hρcs => ?_)
    -- Replace the extension by the indicator, which vanishes off `V` pointwise.
    have e1 : (∫ x, (extendL2 hVm (mulTest hχ w) x : ℝ) * ρ x)
        = ∫ x, Set.indicator V (mulTest hχ w : EuclideanSpace ℝ (Fin d) → ℝ) x * ρ x := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_extendL2 hVm (mulTest hχ w)] with x hx
      rw [hx]
    have e2 : (∫ x, Set.indicator V (mulTest hχ w : EuclideanSpace ℝ (Fin d) → ℝ) x * ρ x)
        = ∫ x in V, Set.indicator V (mulTest hχ w : EuclideanSpace ℝ (Fin d) → ℝ) x * ρ x := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro x hx
      rw [Set.indicator_of_notMem hx, zero_mul]
    have e3 : (∫ x in V, Set.indicator V (mulTest hχ w : EuclideanSpace ℝ (Fin d) → ℝ) x * ρ x)
        = ∫ x in V, (w x : ℝ) * (χ x * ρ x) := by
      refine integral_congr_ae ?_
      filter_upwards [mulTest_coeFn hχ w, ae_restrict_mem hVm] with x h1 h2
      rw [Set.indicator_of_mem h2, h1]
      ring
    rw [e1, e2, e3]
    exact h (fun x => χ x * ρ x) (hχ.1.mul hρcd) hχ.2.1.mul_right
      (tsupport_mul_subset_left.trans hχ.2.2)
  have hnorm : ‖mulTest hχ w‖ = 0 := by
    rw [← norm_extendL2 hVm (mulTest hχ w), hext, norm_zero]
  exact norm_eq_zero.mp hnorm

/-- The difference of two `L²(V)` classes pairs with a test function one term at a time. -/
private theorem setIntegral_sub_mul_testFn_symm {V : Set (EuclideanSpace ℝ (Fin d))}
    {w₁ w₂ : L2D V} {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) :
    (∫ x in V, ((w₁ - w₂) x : ℝ) * φ x)
      = (∫ x in V, (w₁ x : ℝ) * φ x) - ∫ x in V, (w₂ x : ℝ) * φ x := by
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hφL : MemLp φ 2 (volume.restrict V) :=
    (hφc.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hφcs).restrict V
  have hi1 : Integrable (fun x => (w₁ x : ℝ) * φ x) (volume.restrict V) :=
    (Lp.memLp w₁).integrable_mul hφL
  have hi2 : Integrable (fun x => (w₂ x : ℝ) * φ x) (volume.restrict V) :=
    (Lp.memLp w₂).integrable_mul hφL
  have hcong : (∫ x in V, ((w₁ - w₂) x : ℝ) * φ x)
      = ∫ x in V, ((w₁ x : ℝ) * φ x - (w₂ x : ℝ) * φ x) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub w₁ w₂] with x hx
    rw [hx, Pi.sub_apply, sub_mul]
  rw [hcong, integral_sub hi1 hi2]

/-- **Uniqueness of the weak derivative on a region after a cutoff.** Two weak `ℓ`-derivatives of
the same class pair identically with every test function supported in the region, so their
difference is killed by any cutoff supported there.

The region is not asked to be open, which is why the conclusion has the cutoff. A weak
derivative on a set with empty interior is constrained by nothing, and the consumers multiply by
a cutoff regardless. -/
theorem mulTest_weakDerivOn_unique {V : Set (EuclideanSpace ℝ (Fin d))} (hVm : MeasurableSet V)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn V χ) {ℓ : Fin d} {g w₁ w₂ : L2D V}
    (h₁ : HasWeakDerivOn V ℓ g w₁) (h₂ : HasWeakDerivOn V ℓ g w₂) :
    mulTest hχ w₁ = mulTest hχ w₂ := by
  have hkey : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x in V, ((w₁ - w₂) x : ℝ) * φ x = 0 := by
    intro φ hφc hφcs hφV
    rw [setIntegral_sub_mul_testFn_symm hφc hφcs]
    linarith [h₁ φ hφc hφcs hφV, h₂ φ hφc hφcs hφV]
  have hzero := mulTest_eq_zero_of_forall_testFn hVm hχ hkey
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-! ### Mixed second weak derivatives commute -/

/-- **Mixed second weak derivatives commute after a cutoff.** Where `uᵢ` and `u_ℓ` are weak
first derivatives of `u` on `V`, and `u_{ℓi}` is a weak `ℓ`-derivative of `uᵢ` while `u_{iℓ}`
is a weak `i`-derivative of `u_ℓ`, the two agree once multiplied by any test function supported
in `V`.

Two integrations by parts move each of them onto `u`: `∫ u_{ℓi} φ = ∫ u ∂ᵢ∂_ℓφ` and
`∫ u_{iℓ} φ = ∫ u ∂_ℓ∂ᵢφ`, admissibly, since a partial derivative of a test function supported
in `V` is again one. `partialD_comm` identifies the two right-hand sides, so the difference
annihilates every test function supported in `V`. -/
theorem mulTest_mixed_weakDeriv_comm {V : Set (EuclideanSpace ℝ (Fin d))}
    (hVm : MeasurableSet V) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn V χ) {i ℓ : Fin d}
    {u ui ul uli uil : L2D V}
    (hui : HasWeakDerivOn V i u ui) (hul : HasWeakDerivOn V ℓ u ul)
    (huli : HasWeakDerivOn V ℓ ui uli) (huil : HasWeakDerivOn V i ul uil) :
    mulTest hχ uli = mulTest hχ uil := by
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have hkey : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x in V, ((uli - uil) x : ℝ) * φ x = 0 := by
    intro φ hφc hφcs hφV
    obtain ⟨hdℓc, hdℓcs, hdℓV⟩ := isTest_partialD hφc hφcs hφV ℓ
    obtain ⟨hdic, hdics, hdiV⟩ := isTest_partialD hφc hφcs hφV i
    -- Each second derivative, moved onto `u` by two integrations by parts.
    have h1 : (∫ x in V, (uli x : ℝ) * φ x)
        = ∫ x in V, (u x : ℝ) * partialD i (partialD ℓ φ) x := by
      rw [hui (partialD ℓ φ) hdℓc hdℓcs hdℓV]
      linarith [huli φ hφc hφcs hφV]
    have h2 : (∫ x in V, (uil x : ℝ) * φ x)
        = ∫ x in V, (u x : ℝ) * partialD ℓ (partialD i φ) x := by
      rw [hul (partialD i φ) hdic hdics hdiV]
      linarith [huil φ hφc hφcs hφV]
    -- The two right-hand sides agree, so the difference annihilates `φ`.
    rw [setIntegral_sub_mul_testFn_symm hφc hφcs, h1, h2, partialD_comm hφc i ℓ, sub_self]
  have hzero := mulTest_eq_zero_of_forall_testFn hVm hχ hkey
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

end EllipticPdes.Regularity

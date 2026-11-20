/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ComplexRadius
public import LeanPool.FastDynamo.Local.ModifiedBesselKODE
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Cartesian derivatives of the exterior Ponomarenko field

The exterior branch of the `m = 1` Ponomarenko field `(B_r, B_θ, B_3)` is written in Cartesian
coordinates as modified Bessel functions of the radius times powers of the polar phase.  Its
two transverse Cartesian components are the exterior branch of the two-component mode of
Lemma 2.1 (`lem:jump-horizontal-mode`, `Local/HorizontalModeBranches.lean`).  Before that field
can be placed in whole-plane `H¹`, its classical derivative must be computed away from the
origin and shown to decay.  This module supplies the ingredients.

The scalar layer differentiates `K0`, `K1`, and `K2` along positive real rays using the exact
recurrences, and bounds each derivative by an explicit exponential envelope, so that all
three tend to zero at infinity.  The Cartesian layer differentiates the radius, the
complexified radius, and the polar phase `(y₁ + i y₂) / ‖y‖` at every nonzero point, and
computes the exact real-radial derivatives of the three cross-normalized exterior branches.
The physical component derivatives and the Fréchet derivative of the exterior Cartesian field
are assembled from these in `Local/PonomarenkoCartesianExteriorPhysicalDerivative.lean`.

Everything below is a pointwise classical statement together with exponential bounds in a
form ready for the polar-coordinate `L2` argument of
`Local/PonomarenkoExteriorDerivativeDecay.lean`; no weak derivative or Sobolev-membership claim is
made.

## Contents

* Decay of real-radial derivatives of the exterior Bessel branches: the real-radial chain
  rules for `K0`, `K1`, `K2` and their explicit exponential bounds.
* Cartesian derivatives of the exterior Ponomarenko field: the radius and phase
  differentials, the exact real-radial derivatives of the three cross-normalized exterior
  branches, and the exponential `L2`-ready radial bounds.
-/

@[expose] public section

/-!
## Decay of real-radial derivatives of the exterior Bessel branches

The value bounds in `ModifiedBesselBoundaryBehavior` and the exact derivative recurrences in
`ModifiedBesselKODE` imply exponential bounds for the first derivatives of `K0`, `K1`, and
`K2` along every positive real ray in the open right half-plane. No branch-level Cartesian,
Sobolev, or global-mode claim is made in this part.
-/

noncomputable section

namespace FastDynamo
namespace ModifiedBesselDerivativeDecay

open Complex Filter MeasureTheory Set Topology
open ModifiedBesselBoundaryBehavior
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial

/-- Scaling by a positive real number preserves a strictly positive real part: if `Re κ > 0` and
`r > 0` then `Re (κ r) > 0`, so `κ r` stays in the half-plane where `K₀`, `K₁`, `K₂` are
defined. -/
private theorem kappa_mul_real_pos {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) : 0 < (kappa * (r : ℂ)).re := by
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_pos hkappa hr

/-! ## Real-radial chain rules -/

/-- The complex order-zero recurrence restricted to the positive real radial ray. -/
theorem K0_realRadial_hasDerivAt {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ)))
      (kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ)))) r := by
  exact (ModifiedBessel.K0_radial_hasDerivAt kappa (r : ℂ)
    (kappa_mul_real_pos hkappa hr)).comp_ofReal

/-- Derivative of `s ↦ K₀ (κ s)` along the positive real ray: it equals `κ · (-K₁ (κ r))`,
the real-radial form of the standard recurrence `K₀' = -K₁`. -/
theorem deriv_K0_realRadial {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    deriv (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ))) r =
      kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ))) :=
  (K0_realRadial_hasDerivAt hkappa hr).deriv

/-- The complex order-one recurrence restricted to the positive real radial ray. -/
theorem K1_realRadial_hasDerivAt {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ)))
      (kappa * (-(ModifiedBessel.K0 (kappa * (r : ℂ)) +
        ModifiedBessel.K2 (kappa * (r : ℂ))) / 2)) r := by
  exact (ModifiedBessel.K1_radial_hasDerivAt kappa (r : ℂ)
    (kappa_mul_real_pos hkappa hr)).comp_ofReal

/-- Derivative of `s ↦ K₁ (κ s)` along the positive real ray: it equals
`κ · (-(K₀ (κ r) + K₂ (κ r))/2)`, the real-radial form of `2 K₁' = -(K₀ + K₂)`. -/
theorem deriv_K1_realRadial {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))) r =
      kappa * (-(ModifiedBessel.K0 (kappa * (r : ℂ)) +
        ModifiedBessel.K2 (kappa * (r : ℂ))) / 2) :=
  (K1_realRadial_hasDerivAt hkappa hr).deriv

/-- The complex order-two recurrence restricted to the positive real radial ray. -/
theorem K2_realRadial_hasDerivAt {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ)))
      (kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ)) -
        2 / (kappa * (r : ℂ)) * ModifiedBessel.K2 (kappa * (r : ℂ)))) r := by
  exact (ModifiedBessel.K2_radial_hasDerivAt kappa (r : ℂ)
    (kappa_mul_real_pos hkappa hr)).comp_ofReal

/-- Derivative of `s ↦ K₂ (κ s)` along the positive real ray: it equals
`κ · (-K₁ (κ r) - (2/(κ r)) K₂ (κ r))`, the real-radial form of the order-two recurrence. -/
theorem deriv_K2_realRadial {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ))) r =
      kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ)) -
        2 / (kappa * (r : ℂ)) * ModifiedBessel.K2 (kappa * (r : ℂ))) :=
  (K2_realRadial_hasDerivAt hkappa hr).deriv

/-! ## Explicit exponential bounds -/

/-- Explicit exponential bounds for the first real-radial derivatives of all three exterior
Bessel orders.  As in the value bound, every integral on the right is a fixed finite constant
at radius one. -/
theorem modifiedBessel_K012_realRadial_derivative_exponential_bounds
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 1 ≤ r) :
    ‖deriv (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ))) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          (‖kappa‖ * ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖) ∧
      ‖deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          (‖kappa‖ * ((∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K0Integrand kappa t‖) +
            ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖)) ∧
      ‖deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ))) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          (‖kappa‖ * (∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖) +
            2 * (∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖)) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hkappa0 : kappa ≠ 0 := by
    intro hzero
    subst kappa
    simp at hkappa
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  obtain ⟨h0, h1, h2⟩ := modifiedBessel_K012_radial_exponential_bounds hkappa hr
  let E : ℝ := Real.exp (-kappa.re * (r - 1))
  let C0 : ℝ := ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K0Integrand kappa t‖
  let C1 : ℝ := ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖
  let C2 : ℝ := ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖
  change ‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ ≤ E * C0 at h0
  change ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖ ≤ E * C1 at h1
  change ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤ E * C2 at h2
  have hcoef : ‖(2 : ℂ) / (r : ℂ)‖ ≤ 2 := by
    rw [norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [div_le_iff₀ hrpos]
    nlinarith
  constructor
  · rw [deriv_K0_realRadial hkappa hrpos, norm_mul, norm_neg]
    change ‖kappa‖ * ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖ ≤ E * (‖kappa‖ * C1)
    calc
      ‖kappa‖ * ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖ ≤ ‖kappa‖ * (E * C1) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = E * (‖kappa‖ * C1) := by ring
  constructor
  · rw [deriv_K1_realRadial hkappa hrpos, norm_mul]
    change ‖kappa‖ * ‖-(ModifiedBessel.K0 (kappa * (r : ℂ)) +
        ModifiedBessel.K2 (kappa * (r : ℂ))) / 2‖ ≤ E * (‖kappa‖ * (C0 + C2))
    calc
      ‖kappa‖ * ‖-(ModifiedBessel.K0 (kappa * (r : ℂ)) +
          ModifiedBessel.K2 (kappa * (r : ℂ))) / 2‖ ≤
          ‖kappa‖ * (‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ +
            ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc
          ‖-(ModifiedBessel.K0 (kappa * (r : ℂ)) +
              ModifiedBessel.K2 (kappa * (r : ℂ))) / 2‖ =
              ‖ModifiedBessel.K0 (kappa * (r : ℂ)) +
                ModifiedBessel.K2 (kappa * (r : ℂ))‖ / 2 := by
              rw [norm_div, norm_neg]
              norm_num
          _ ≤ (‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ +
                ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖) / 2 := by
              gcongr
              exact norm_add_le _ _
          _ ≤ ‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ +
                ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ := by
              nlinarith [norm_nonneg (ModifiedBessel.K0 (kappa * (r : ℂ))),
                norm_nonneg (ModifiedBessel.K2 (kappa * (r : ℂ)))]
      _ ≤ ‖kappa‖ * (E * C0 + E * C2) := by
        gcongr
      _ = E * (‖kappa‖ * (C0 + C2)) := by ring
  · rw [deriv_K2_realRadial hkappa hrpos]
    have hrewrite :
        kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ)) -
            2 / (kappa * (r : ℂ)) * ModifiedBessel.K2 (kappa * (r : ℂ))) =
          -kappa * ModifiedBessel.K1 (kappa * (r : ℂ)) -
            2 / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ)) := by
      field_simp [hkappa0, hr0]
    rw [hrewrite]
    change ‖-kappa * ModifiedBessel.K1 (kappa * (r : ℂ)) -
        2 / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤
      E * (‖kappa‖ * C1 + 2 * C2)
    calc
      ‖-kappa * ModifiedBessel.K1 (kappa * (r : ℂ)) -
          2 / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤
          ‖kappa‖ * ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖ +
            ‖(2 : ℂ) / (r : ℂ)‖ *
              ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ := by
        simpa only [norm_mul, norm_neg] using norm_sub_le
          (-kappa * ModifiedBessel.K1 (kappa * (r : ℂ)))
          (2 / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ)))
      _ ≤ ‖kappa‖ * (E * C1) + 2 * (E * C2) := by
        gcongr
      _ = E * (‖kappa‖ * C1 + 2 * C2) := by ring

end ModifiedBesselDerivativeDecay
end FastDynamo

/-!
## Cartesian derivatives of the exterior Ponomarenko field

The physical exterior Cartesian formula is differentiated here on the punctured transverse
plane.  The radial derivative recurrences for `K0`,
`K1`, and `K2` above are combined with the elementary derivative of the polar phase
`(y₁ + i y₂) / ‖y‖`.

The resulting identities are pointwise classical Fréchet-derivative
statements.  Exponential estimates are also recorded for the scalar radial
branches, in a form ready for the later polar-coordinate `L2` argument.  No
weak derivative or Sobolev-membership claim is made here.
-/

noncomputable section

namespace FastDynamo
namespace PonomarenkoCartesianExteriorDerivative

open Complex Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial
open ComplexRadius
open CartesianRadialRegularity
open ModifiedBesselBoundaryBehavior
open ModifiedBesselDerivativeDecay

/-! ## The radius and phase differentials -/

/-- The real differential of the Euclidean radius at a nonzero point.  The
formula is totalized, but its derivative theorem is used only for `y ≠ 0`. -/
def radiusDerivative (y : WholePlane) : WholePlane →L[ℝ] ℝ :=
  (1 / (2 * ‖y‖)) • (2 • innerSL ℝ y)

/-- The differential of the complex-valued physical radius. -/
def complexRadiusDerivative (y : WholePlane) : WholePlane →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (radiusDerivative y)

/-- The physical polar phase `q = (y₁ + i y₂) / ‖y‖`. -/
def exteriorPhase (y : WholePlane) : ℂ :=
  complexCoordinate y / complexRadius y

/-- The differential of the physical phase, written without hiding the
angular `1 / r` factor. -/
def exteriorPhaseDerivative (y : WholePlane) : WholePlane →L[ℝ] ℂ :=
  (complexRadius y)⁻¹ • complexCoordinateCLM -
    (complexCoordinate y / complexRadius y ^ 2) • complexRadiusDerivative y

/-- Away from the origin the Euclidean radius `y ↦ ‖y‖` is Fréchet differentiable with
differential `radiusDerivative y`, that is `v ↦ ⟪y, v⟫ / ‖y‖`. -/
theorem radius_hasFDerivAt {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt (fun x : WholePlane ↦ ‖x‖) (radiusDerivative y) y := by
  have hsq := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hnonzero : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hsqrt := hsq.sqrt hnonzero
  have heq : (fun x : WholePlane ↦ Real.sqrt (‖x‖ ^ 2)) = fun x ↦ ‖x‖ := by
    funext x
    rw [Real.sqrt_sq (norm_nonneg x)]
  rw [heq] at hsqrt
  simpa only [radiusDerivative, Real.sqrt_sq (norm_nonneg y)] using hsqrt

/-- Away from the origin the complex-valued radius is Fréchet differentiable with the
complexification of the radius differential. -/
theorem complexRadius_hasFDerivAt {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt complexRadius (complexRadiusDerivative y) y := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp y (radius_hasFDerivAt hy)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x ↦ rfl

/-- Evaluation of the radius differential: `radiusDerivative y v = ⟪y, v⟫ / ‖y‖`. -/
@[simp] theorem radiusDerivative_apply (y v : WholePlane) :
    radiusDerivative y v = (inner ℝ y v) / ‖y‖ := by
  simp [radiusDerivative]
  ring

/-- Evaluation of the complex radius differential: the real value `⟪y, v⟫ / ‖y‖` viewed in `ℂ`. -/
@[simp] theorem complexRadiusDerivative_apply (y v : WholePlane) :
    complexRadiusDerivative y v = (((inner ℝ y v) / ‖y‖ : ℝ) : ℂ) := by
  simp [complexRadiusDerivative]

/-- Away from the origin the polar phase `q = (y₀ + i y₁)/‖y‖` is Fréchet differentiable with
differential `exteriorPhaseDerivative y`, obtained from the quotient rule. -/
theorem exteriorPhase_hasFDerivAt {y : WholePlane} (hy : y ≠ 0) :
    HasFDerivAt exteriorPhase (exteriorPhaseDerivative y) y := by
  have hr0 : complexRadius y ≠ 0 := by
    exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hinv := (hasFDerivAt_inv' (𝕜 := ℝ) hr0).comp y
    (complexRadius_hasFDerivAt hy)
  have hmul := (complexCoordinate_hasFDerivAt y).mul hinv
  have hfun : HasFDerivAt exteriorPhase
      (complexCoordinate y •
          ((-((ContinuousLinearMap.mulLeftRight ℝ ℂ)
            (complexRadius y)⁻¹) (complexRadius y)⁻¹) ∘L
              complexRadiusDerivative y) +
        (complexRadius y)⁻¹ • complexCoordinateCLM) y := by
    apply hmul.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x ↦ by
      simp [exteriorPhase, div_eq_mul_inv]
  convert hfun using 1
  ext v
  simp [exteriorPhaseDerivative, div_eq_mul_inv]
  field_simp [hr0]
  ring

/-- The complex coordinate has exactly the physical Euclidean radius as its
norm. -/
theorem norm_complexCoordinate (y : WholePlane) :
    ‖complexCoordinate y‖ = ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [complexCoordinate, Complex.normSq_apply, Fin.sum_univ_two]
  ring

/-- The complex radius has the Euclidean radius as its modulus. -/
@[simp] theorem norm_complexRadius (y : WholePlane) :
    ‖complexRadius y‖ = ‖y‖ := by
  simp [complexRadius]

/-- Away from the axis the physical phase lies on the complex unit circle. -/
theorem norm_exteriorPhase {y : WholePlane} (hy : y ≠ 0) :
    ‖exteriorPhase y‖ = 1 := by
  rw [exteriorPhase, norm_div, norm_complexCoordinate, norm_complexRadius]
  exact div_self (norm_ne_zero_iff.mpr hy)

/-- Coordinate evaluation of the phase differential:
`∂ⱼ q = eⱼ / r - z yⱼ / r³` with `e₀ = 1`, `e₁ = i`. -/
@[simp] theorem exteriorPhaseDerivative_basis (y : WholePlane) (j : Fin 2) :
    exteriorPhaseDerivative y (wholePlaneBasis j) =
      ((if j = 0 then 1 else I) / complexRadius y) -
        complexCoordinate y * ((y j : ℂ) / (complexRadius y ^ 3)) := by
  by_cases hj : j = 0
  · subst j
    simp only [exteriorPhaseDerivative, sub_apply,
      smul_apply, complexCoordinateCLM_basis_zero,
      complexRadiusDerivative_apply, inner_wholePlaneBasis, ite_eq_left]
    simp [complexRadius]
    ring
  · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj
    subst j
    simp only [exteriorPhaseDerivative, sub_apply,
      smul_apply, complexCoordinateCLM_basis_one,
      complexRadiusDerivative_apply, inner_wholePlaneBasis,
      ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
    simp [complexRadius]
    ring

/-- Each physical Cartesian derivative of the angular phase is bounded by
`2 / r`.  This is the precise harmless angular factor needed on the exterior
region `r ≥ 1`. -/
theorem norm_exteriorPhaseDerivative_basis_le
    {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    ‖exteriorPhaseDerivative y (wholePlaneBasis j)‖ ≤ 2 / ‖y‖ := by
  have hrpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hunit : ‖(if j = 0 then (1 : ℂ) else I)‖ = 1 := by
    by_cases hj : j = 0 <;> simp [hj]
  have hcoord : ‖(y j : ℂ)‖ ≤ ‖y‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using PiLp.norm_apply_le y j
  have hfirst :
      ‖(if j = 0 then (1 : ℂ) else I) / complexRadius y‖ = 1 / ‖y‖ := by
    rw [norm_div, hunit, norm_complexRadius]
  have hsecond :
      ‖complexCoordinate y * ((y j : ℂ) / complexRadius y ^ 3)‖ ≤
        1 / ‖y‖ := by
    rw [norm_mul, norm_div, norm_complexCoordinate, norm_pow, norm_complexRadius]
    calc
      ‖y‖ * (‖(y j : ℂ)‖ / ‖y‖ ^ 3) ≤
          ‖y‖ * (‖y‖ / ‖y‖ ^ 3) := by gcongr
      _ = 1 / ‖y‖ := by field_simp [ne_of_gt hrpos]
  rw [exteriorPhaseDerivative_basis]
  calc
    ‖(if j = 0 then (1 : ℂ) else I) / complexRadius y -
        complexCoordinate y * ((y j : ℂ) / complexRadius y ^ 3)‖ ≤
        ‖(if j = 0 then (1 : ℂ) else I) / complexRadius y‖ +
          ‖complexCoordinate y * ((y j : ℂ) / complexRadius y ^ 3)‖ :=
      norm_sub_le _ _
    _ ≤ 1 / ‖y‖ + 1 / ‖y‖ := by rw [hfirst]; gcongr
    _ = 2 / ‖y‖ := by ring
/-! ## Exact real-radial derivatives of the three exterior branches -/

/-- The order-two exterior circular branch on the physical real radius. -/
def plusOutsideReal (kappa : ℂ) (r : ℝ) : ℂ :=
  plusOutside kappa (r : ℂ)

/-- The order-zero exterior circular branch on the physical real radius. -/
def minusOutsideReal (kappa : ℂ) (r : ℝ) : ℂ :=
  minusOutside kappa (r : ℂ)

/-- The axial exterior branch on the physical real radius. -/
def axialOutsideReal (N : ℝ) (kappa : ℂ) (r : ℝ) : ℂ :=
  axialOutside N kappa (r : ℂ)

/-- Radial derivative of the order-two exterior branch on the positive real ray, from the
second-kind recurrence for `K₂`. -/
theorem plusOutsideReal_hasDerivAt {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (plusOutsideReal kappa)
      (ModifiedBessel.I2 kappa *
        (kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ)) -
          2 / (kappa * (r : ℂ)) * ModifiedBessel.K2 (kappa * (r : ℂ))))) r := by
  unfold plusOutsideReal plusOutside
  exact (K2_realRadial_hasDerivAt hkappa hr).const_mul _

/-- Radial derivative of the order-zero exterior branch on the positive real ray, from
`K₀' = -K₁`. -/
theorem minusOutsideReal_hasDerivAt {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (minusOutsideReal kappa)
      (-ModifiedBessel.I0 kappa *
        (kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ))))) r := by
  unfold minusOutsideReal minusOutside
  exact (K0_realRadial_hasDerivAt hkappa hr).const_mul _

/-- Radial derivative of the axial exterior branch on the positive real ray, from
`2 K₁' = -(K₀ + K₂)` and the normalization by `i N`. -/
theorem axialOutsideReal_hasDerivAt (N : ℝ) {kappa : ℂ}
    (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (axialOutsideReal N kappa)
      ((-(ModifiedBessel.I1 kappa *
        (kappa * (-(ModifiedBessel.K0 (kappa * (r : ℂ)) +
          ModifiedBessel.K2 (kappa * (r : ℂ))) / 2)))) / (I * (N : ℂ))) r := by
  unfold axialOutsideReal axialOutside
  exact ((K1_realRadial_hasDerivAt hkappa hr).const_mul _).neg.div_const _

/-! ## Exponential, `L2`-ready radial bounds -/

/-- Simultaneous exponential bounds for the three cross-normalized exterior
radial derivatives.  The constants depend only on `N` and `kappa`, while the
entire radius dependence is the integrable exponential factor. -/
theorem exterior_branch_derivative_exponential_bounds
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re)
    {r : ℝ} (hr : 1 ≤ r) :
    ‖deriv (plusOutsideReal kappa) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          (‖ModifiedBessel.I2 kappa‖ *
            (‖kappa‖ * (∫ t in Ioi (0 : ℝ),
              ‖ModifiedBessel.K1Integrand kappa t‖) +
              2 * (∫ t in Ioi (0 : ℝ),
                ‖ModifiedBessel.K2Integrand kappa t‖))) ∧
      ‖deriv (minusOutsideReal kappa) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          (‖ModifiedBessel.I0 kappa‖ * ‖kappa‖ *
            ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖) ∧
      ‖deriv (axialOutsideReal N kappa) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) *
          (‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
            (‖kappa‖ * ((∫ t in Ioi (0 : ℝ),
              ‖ModifiedBessel.K0Integrand kappa t‖) +
              ∫ t in Ioi (0 : ℝ),
                ‖ModifiedBessel.K2Integrand kappa t‖))) := by
  obtain ⟨h0, h1, h2⟩ :=
    modifiedBessel_K012_realRadial_derivative_exponential_bounds hkappa hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hp := plusOutsideReal_hasDerivAt hkappa hrpos
  have hm := minusOutsideReal_hasDerivAt hkappa hrpos
  have ha := axialOutsideReal_hasDerivAt N hkappa hrpos
  constructor
  · rw [hp.deriv, norm_mul]
    rw [show kappa * (-ModifiedBessel.K1 (kappa * (r : ℂ)) -
        2 / (kappa * (r : ℂ)) * ModifiedBessel.K2 (kappa * (r : ℂ))) =
        deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ))) r by
          exact (deriv_K2_realRadial hkappa hrpos).symm]
    calc
      ‖ModifiedBessel.I2 kappa‖ *
          ‖deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ))) r‖ ≤
          ‖ModifiedBessel.I2 kappa‖ *
            (Real.exp (-kappa.re * (r - 1)) *
              (‖kappa‖ * (∫ t in Ioi (0 : ℝ),
                ‖ModifiedBessel.K1Integrand kappa t‖) +
                2 * (∫ t in Ioi (0 : ℝ),
                  ‖ModifiedBessel.K2Integrand kappa t‖))) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg (ModifiedBessel.I2 kappa))
      _ = _ := by ring
  constructor
  · rw [hm.deriv, norm_mul, norm_neg]
    calc
      ‖ModifiedBessel.I0 kappa‖ *
          ‖kappa * -ModifiedBessel.K1 (kappa * (r : ℂ))‖ =
          ‖ModifiedBessel.I0 kappa‖ *
            ‖deriv (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ))) r‖ := by
              rw [deriv_K0_realRadial hkappa hrpos]
      _ ≤ ‖ModifiedBessel.I0 kappa‖ *
          (Real.exp (-kappa.re * (r - 1)) *
            (‖kappa‖ * ∫ t in Ioi (0 : ℝ),
              ‖ModifiedBessel.K1Integrand kappa t‖)) :=
            mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
      _ = _ := by ring
  · rw [ha.deriv]
    have heq :
        ‖-(ModifiedBessel.I1 kappa *
            deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))) r) /
            (I * (N : ℂ))‖ =
          ‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
            ‖deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))) r‖ := by
      rw [norm_div, norm_neg, norm_mul, norm_div]
      ring
    rw [show kappa * (-(ModifiedBessel.K0 (kappa * (r : ℂ)) +
        ModifiedBessel.K2 (kappa * (r : ℂ))) / 2) =
        deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))) r by
          exact (deriv_K1_realRadial hkappa hrpos).symm]
    rw [heq]
    calc
      ‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
          ‖deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))) r‖ ≤
          ‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
            (Real.exp (-kappa.re * (r - 1)) *
              (‖kappa‖ * ((∫ t in Ioi (0 : ℝ),
                ‖ModifiedBessel.K0Integrand kappa t‖) +
                ∫ t in Ioi (0 : ℝ),
                  ‖ModifiedBessel.K2Integrand kappa t‖))) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by ring

end PonomarenkoCartesianExteriorDerivative
end FastDynamo

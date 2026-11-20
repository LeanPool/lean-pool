/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorPhysicalDerivative
public import LeanPool.FastDynamo.Analysis.WholePlaneRadialExponential

/-!
# Second radial derivatives of the exterior Ponomarenko branches

The second derivatives of the exterior (decaying Bessel) branches of the Ponomarenko mode of
`lem:jump-horizontal-mode`, as one-dimensional radial identities with exponential bounds, and
the smoothness away from the origin of the scalar ingredients of the exterior Cartesian
formulas.

The radial layer differentiates the real-ray `K0`, `K1`, and `K2` formulas a second time,
transfers the result to the three cross-normalized exterior branches, and bounds them by a
common exponential envelope `exp(-(Re κ)(r - 1))` on `r ≥ 1`.  The Cartesian layer proves
that the complex radius and the exterior phase are smooth at every nonzero point.  The
envelope constants are consumed by `Local/PonomarenkoExteriorSecondPartialBounds.lean`, and the
smoothness of the exterior phase by `Local/HorizontalModeSecondDerivatives.lean` and
`Local/PonomarenkoCartesianPolarLaplacian.lean`.

No `H2` regularity across the radius-one interface is claimed anywhere here.

## Contents

* Second radial derivatives of the exterior Ponomarenko branches: the exact second
  derivatives of `K0`, `K1`, `K2` on positive real rays, their transfer to the
  cross-normalized branches, and the explicit exponential bounds
  `exterior_branch_secondDerivative_exponential_bounds`.
* Smoothness of the scalar exterior ingredients: `complexRadius_contDiffAt_infty` and
  `exteriorPhase_contDiffAt_infty`.
-/

@[expose] public section

/-!
## Second radial derivatives of the exterior Ponomarenko branches

The radial part of the exterior `H2` calculation.  The real-ray `K0`, `K1`, and `K2`
formulas are differentiated a second time.
The denominator-free forms below are particularly convenient on the physical
exterior region `r ≥ 1`.  They are then transferred to the three
cross-normalized Ponomarenko branches and bounded by a common radial
exponential envelope.

These are branchwise, classical statements.  In particular,
nothing here asserts that the full piecewise Cartesian field belongs to
`H2`; the angular Hessian terms and the interface weak-derivative argument
are not part of this module.
-/

noncomputable section

namespace FastDynamo
namespace PonomarenkoCartesianExteriorSecondDerivative

open Complex Filter MeasureTheory Set Topology
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial
open PonomarenkoCartesianExteriorDerivative
open ModifiedBesselBoundaryBehavior
open ModifiedBesselDerivativeDecay
open WholePlaneRadialExponential

/-! ## Exact second derivatives on positive real rays -/

/-- Positivity is an open condition: if `r > 0` then `s > 0` for all `s` near `r`.  This is what
lets the real-ray recurrences be differentiated a second time. -/
private theorem eventually_pos_nhds {r : ℝ} (hr : 0 < r) :
    ∀ᶠ s in nhds r, 0 < s :=
  isOpen_Ioi.mem_nhds hr

/-- The second derivative of `K0 (kappa r)` along the positive real ray. -/
theorem K0_realRadial_second_hasDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (deriv (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ))))
      (kappa ^ 2 *
        ((ModifiedBessel.K0 (kappa * (r : ℂ)) +
          ModifiedBessel.K2 (kappa * (r : ℂ))) / 2)) r := by
  have h := (K1_realRadial_hasDerivAt hkappa hr).neg.const_mul kappa
  have heq :
      deriv (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ))) =ᶠ[nhds r]
        fun s : ℝ ↦ kappa * (-ModifiedBessel.K1 (kappa * (s : ℂ))) := by
    filter_upwards [eventually_pos_nhds hr] with s hs
    exact deriv_K0_realRadial hkappa hs
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

/-- Value form of the second real-radial derivative of `K₀(κ s)`:
`κ² (K₀(κ r) + K₂(κ r))/2`. -/
theorem deriv_deriv_K0_realRadial
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ)))) r =
      kappa ^ 2 *
        ((ModifiedBessel.K0 (kappa * (r : ℂ)) +
          ModifiedBessel.K2 (kappa * (r : ℂ))) / 2) :=
  (K0_realRadial_second_hasDerivAt hkappa hr).deriv

/-- The second derivative of `K1 (kappa r)` along the positive real ray,
written without division by `kappa`. -/
theorem K1_realRadial_second_hasDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))))
      (kappa ^ 2 * ModifiedBessel.K1 (kappa * (r : ℂ)) +
        kappa / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ))) r := by
  have hkappa0 : kappa ≠ 0 := by
    intro hzero
    subst kappa
    simp at hkappa
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := (((K0_realRadial_hasDerivAt hkappa hr).add
    (K2_realRadial_hasDerivAt hkappa hr)).neg.div_const 2).const_mul kappa
  have heq :
      deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ))) =ᶠ[nhds r]
        fun s : ℝ ↦ kappa *
          (-(ModifiedBessel.K0 (kappa * (s : ℂ)) +
            ModifiedBessel.K2 (kappa * (s : ℂ))) / 2) := by
    filter_upwards [eventually_pos_nhds hr] with s hs
    exact deriv_K1_realRadial hkappa hs
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  field_simp [hkappa0, hr0]
  ring

/-- Value form of the second real-radial derivative of `K₁(κ s)`:
`κ² K₁(κ r) + (κ/r) K₂(κ r)`, written without division by `κ`. -/
theorem deriv_deriv_K1_realRadial
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ)))) r =
      kappa ^ 2 * ModifiedBessel.K1 (kappa * (r : ℂ)) +
        kappa / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ)) :=
  (K1_realRadial_second_hasDerivAt hkappa hr).deriv

/-- The derivative of the real-ray coefficient `2 / r`. -/
private theorem two_div_real_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ ↦ (2 : ℂ) / (s : ℂ))
      (-2 / (r : ℂ) ^ 2) r := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcomplex : HasDerivAt (fun z : ℂ ↦ (2 : ℂ) / z)
      (-2 / (r : ℂ) ^ 2) (r : ℂ) := by
    apply ((hasDerivAt_const (r : ℂ) (2 : ℂ)).div
      (hasDerivAt_id (r : ℂ)) hr0).congr_deriv
    simp only [id_eq]
    field_simp [hr0]; ring
  exact hcomplex.comp_ofReal

/-- The second derivative of `K2 (kappa r)` along the positive real ray.  All
inverse powers involve only the physical radius. -/
theorem K2_realRadial_second_hasDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ))))
      (kappa ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)) +
        kappa / (r : ℂ) * ModifiedBessel.K1 (kappa * (r : ℂ)) +
        6 / (r : ℂ) ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ))) r := by
  have hkappa0 : kappa ≠ 0 := by
    intro hzero
    subst kappa
    simp at hkappa
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hfirst := (K1_realRadial_hasDerivAt hkappa hr).const_mul (-kappa)
  have hsecond := (two_div_real_hasDerivAt hr).mul
    (K2_realRadial_hasDerivAt hkappa hr)
  have h := hfirst.sub hsecond
  have heq :
      deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ))) =ᶠ[nhds r]
        fun s : ℝ ↦
          -kappa * ModifiedBessel.K1 (kappa * (s : ℂ)) -
            (2 : ℂ) / (s : ℂ) *
              ModifiedBessel.K2 (kappa * (s : ℂ)) := by
    filter_upwards [eventually_pos_nhds hr] with s hs
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [deriv_K2_realRadial hkappa hs]
    field_simp [hkappa0, hs0]
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  rw [ModifiedBessel.K1_eq_z_div_two_mul_K2_sub_K0
    (show 0 < (kappa * (r : ℂ)).re by
      simpa [Complex.mul_re] using mul_pos hkappa hr)]
  field_simp [hkappa0, hr0]
  ring

/-- Value form of the second real-radial derivative of `K₂(κ s)`:
`κ² K₂(κ r) + (κ/r) K₁(κ r) + (6/r²) K₂(κ r)`, all inverse powers involving only the physical
radius. -/
theorem deriv_deriv_K2_realRadial
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ)))) r =
      kappa ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)) +
        kappa / (r : ℂ) * ModifiedBessel.K1 (kappa * (r : ℂ)) +
        6 / (r : ℂ) ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)) :=
  (K2_realRadial_second_hasDerivAt hkappa hr).deriv

/-! ## Second derivatives of the cross-normalized branches -/

/-- Second real-radial derivative of the cross-normalized exterior order-two branch
`r ↦ I₂(κ) K₂(κ r)`, obtained from the second derivative of `K₂` along the ray. -/
theorem plusOutsideReal_second_hasDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (plusOutsideReal kappa))
      (ModifiedBessel.I2 kappa *
        (kappa ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)) +
          kappa / (r : ℂ) * ModifiedBessel.K1 (kappa * (r : ℂ)) +
          6 / (r : ℂ) ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)))) r := by
  have h := (K2_realRadial_second_hasDerivAt hkappa hr).const_mul
    (ModifiedBessel.I2 kappa)
  have heq : deriv (plusOutsideReal kappa) =ᶠ[nhds r]
      fun s : ℝ ↦ ModifiedBessel.I2 kappa *
        deriv (fun t : ℝ ↦ ModifiedBessel.K2 (kappa * (t : ℂ))) s := by
    filter_upwards [eventually_pos_nhds hr] with s hs
    rw [(plusOutsideReal_hasDerivAt hkappa hs).deriv,
      deriv_K2_realRadial hkappa hs]
  exact h.congr_of_eventuallyEq heq

/-- Second real-radial derivative of the cross-normalized exterior order-zero branch
`r ↦ -I₀(κ) K₀(κ r)`, obtained from the second derivative of `K₀` along the ray. -/
theorem minusOutsideReal_second_hasDerivAt
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (minusOutsideReal kappa))
      (-ModifiedBessel.I0 kappa *
        (kappa ^ 2 *
          ((ModifiedBessel.K0 (kappa * (r : ℂ)) +
            ModifiedBessel.K2 (kappa * (r : ℂ))) / 2))) r := by
  have h := (K0_realRadial_second_hasDerivAt hkappa hr).const_mul
    (-ModifiedBessel.I0 kappa)
  have heq : deriv (minusOutsideReal kappa) =ᶠ[nhds r]
      fun s : ℝ ↦ -ModifiedBessel.I0 kappa *
        deriv (fun t : ℝ ↦ ModifiedBessel.K0 (kappa * (t : ℂ))) s := by
    filter_upwards [eventually_pos_nhds hr] with s hs
    rw [(minusOutsideReal_hasDerivAt hkappa hs).deriv,
      deriv_K0_realRadial hkappa hs]
  exact h.congr_of_eventuallyEq heq

/-- Second real-radial derivative of the cross-normalized exterior axial branch, obtained from
the second derivative of `K₁` along the ray and the normalization by `i N`. -/
theorem axialOutsideReal_second_hasDerivAt
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (axialOutsideReal N kappa))
      ((-(ModifiedBessel.I1 kappa *
        (kappa ^ 2 * ModifiedBessel.K1 (kappa * (r : ℂ)) +
          kappa / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ))))) /
          (I * (N : ℂ))) r := by
  have h := ((K1_realRadial_second_hasDerivAt hkappa hr).const_mul
    (ModifiedBessel.I1 kappa)).neg.div_const (I * (N : ℂ))
  have heq : deriv (axialOutsideReal N kappa) =ᶠ[nhds r]
      fun s : ℝ ↦
        -(ModifiedBessel.I1 kappa *
          deriv (fun t : ℝ ↦ ModifiedBessel.K1 (kappa * (t : ℂ))) s) /
            (I * (N : ℂ)) := by
    filter_upwards [eventually_pos_nhds hr] with s hs
    rw [(axialOutsideReal_hasDerivAt N hkappa hs).deriv,
      deriv_K1_realRadial hkappa hs]
  exact h.congr_of_eventuallyEq heq

/-- Value form of the second radial derivative of the exterior order-two branch. -/
theorem deriv_deriv_plusOutsideReal
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (plusOutsideReal kappa)) r =
      ModifiedBessel.I2 kappa *
        (kappa ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)) +
          kappa / (r : ℂ) * ModifiedBessel.K1 (kappa * (r : ℂ)) +
          6 / (r : ℂ) ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ))) :=
  (plusOutsideReal_second_hasDerivAt hkappa hr).deriv

/-- Value form of the second radial derivative of the exterior order-zero branch. -/
theorem deriv_deriv_minusOutsideReal
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (minusOutsideReal kappa)) r =
      -ModifiedBessel.I0 kappa *
        (kappa ^ 2 *
          ((ModifiedBessel.K0 (kappa * (r : ℂ)) +
            ModifiedBessel.K2 (kappa * (r : ℂ))) / 2)) :=
  (minusOutsideReal_second_hasDerivAt hkappa hr).deriv

/-- Value form of the second radial derivative of the exterior axial branch. -/
theorem deriv_deriv_axialOutsideReal
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (axialOutsideReal N kappa)) r =
      (-(ModifiedBessel.I1 kappa *
        (kappa ^ 2 * ModifiedBessel.K1 (kappa * (r : ℂ)) +
          kappa / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ))))) /
            (I * (N : ℂ)) :=
  (axialOutsideReal_second_hasDerivAt N hkappa hr).deriv

/-! ## Exponential bounds -/

/-- Radius-one envelope constants for the second derivatives of `K0`, `K1`,
and `K2` along the ray `kappa r`. -/
def K0SecondDerivativeConstant (kappa : ℂ) : ℝ :=
  ‖kappa‖ ^ 2 *
    ((∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K0Integrand kappa t‖) +
      ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖)

/-- Radius-one exponential-envelope constant for the second derivative of `K1 (kappa r)`. -/
def K1SecondDerivativeConstant (kappa : ℂ) : ℝ :=
  ‖kappa‖ ^ 2 *
      (∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖) +
    ‖kappa‖ *
      (∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖)

/-- Radius-one exponential-envelope constant for the second derivative of `K2 (kappa r)`. -/
def K2SecondDerivativeConstant (kappa : ℂ) : ℝ :=
  ‖kappa‖ ^ 2 *
      (∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖) +
    ‖kappa‖ *
      (∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖) +
    6 * (∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖)

/-- The radius-one envelope constant for the second derivative of `K₀(κ r)` is nonnegative. -/
theorem K0SecondDerivativeConstant_nonneg (kappa : ℂ) :
    0 ≤ K0SecondDerivativeConstant kappa := by
  unfold K0SecondDerivativeConstant
  positivity

/-- The radius-one envelope constant for the second derivative of `K₂(κ r)` is nonnegative. -/
theorem K2SecondDerivativeConstant_nonneg (kappa : ℂ) :
    0 ≤ K2SecondDerivativeConstant kappa := by
  unfold K2SecondDerivativeConstant
  positivity

/-- On the exterior region `r ≥ 1` the coefficient `κ/r` is bounded in norm by `‖κ‖`. -/
private theorem norm_kappa_div_real_le
    (kappa : ℂ) {r : ℝ} (hr : 1 ≤ r) :
    ‖kappa / (r : ℂ)‖ ≤ ‖kappa‖ := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  exact div_le_self (norm_nonneg kappa) (by linarith)

/-- On the exterior region `r ≥ 1` the coefficient `6/r²` is bounded in norm by `6`. -/
private theorem norm_six_div_real_sq_le {r : ℝ} (hr : 1 ≤ r) :
    ‖(6 : ℂ) / (r : ℂ) ^ 2‖ ≤ 6 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [norm_div, norm_ofNat, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos hrpos]
  apply div_le_self (by norm_num : (0 : ℝ) ≤ 6)
  nlinarith

/-- Simultaneous exponential bounds for the second real-radial derivatives of
the three modified-Bessel factors. -/
theorem modifiedBessel_K012_realRadial_secondDerivative_exponential_bounds
    {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 1 ≤ r) :
    ‖deriv (deriv (fun s : ℝ ↦ ModifiedBessel.K0 (kappa * (s : ℂ)))) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) * K0SecondDerivativeConstant kappa ∧
      ‖deriv (deriv (fun s : ℝ ↦ ModifiedBessel.K1 (kappa * (s : ℂ)))) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) * K1SecondDerivativeConstant kappa ∧
      ‖deriv (deriv (fun s : ℝ ↦ ModifiedBessel.K2 (kappa * (s : ℂ)))) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) * K2SecondDerivativeConstant kappa := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  obtain ⟨h0, h1, h2⟩ :=
    modifiedBessel_K012_radial_exponential_bounds hkappa hr
  let E : ℝ := Real.exp (-kappa.re * (r - 1))
  let C0 : ℝ := ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K0Integrand kappa t‖
  let C1 : ℝ := ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K1Integrand kappa t‖
  let C2 : ℝ := ∫ t in Ioi (0 : ℝ), ‖ModifiedBessel.K2Integrand kappa t‖
  change ‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ ≤ E * C0 at h0
  change ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖ ≤ E * C1 at h1
  change ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤ E * C2 at h2
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  have hkr := norm_kappa_div_real_le kappa hr
  have hsix := norm_six_div_real_sq_le hr
  constructor
  · rw [deriv_deriv_K0_realRadial hkappa hrpos, norm_mul, norm_pow]
    change ‖kappa‖ ^ 2 *
        ‖(ModifiedBessel.K0 (kappa * (r : ℂ)) +
          ModifiedBessel.K2 (kappa * (r : ℂ))) / 2‖ ≤
      E * K0SecondDerivativeConstant kappa
    calc
      _ ≤ ‖kappa‖ ^ 2 *
          (‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ +
            ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖) := by
        gcongr
        rw [norm_div]
        norm_num
        calc
          ‖ModifiedBessel.K0 (kappa * (r : ℂ)) +
              ModifiedBessel.K2 (kappa * (r : ℂ))‖ / 2 ≤
              (‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ +
                ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖) / 2 := by
            gcongr
            exact norm_add_le _ _
          _ ≤ ‖ModifiedBessel.K0 (kappa * (r : ℂ))‖ +
                ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ :=
            div_le_self (add_nonneg (norm_nonneg _) (norm_nonneg _))
              (by norm_num)
      _ ≤ ‖kappa‖ ^ 2 * (E * C0 + E * C2) := by gcongr
      _ = E * K0SecondDerivativeConstant kappa := by
        simp only [K0SecondDerivativeConstant, C0, C2]
        ring
  constructor
  · rw [deriv_deriv_K1_realRadial hkappa hrpos]
    change ‖kappa ^ 2 * ModifiedBessel.K1 (kappa * (r : ℂ)) +
        kappa / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤
      E * K1SecondDerivativeConstant kappa
    calc
      _ ≤ ‖kappa‖ ^ 2 * ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖ +
          ‖kappa / (r : ℂ)‖ *
            ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ := by
        calc
          _ ≤ ‖kappa ^ 2 * ModifiedBessel.K1 (kappa * (r : ℂ))‖ +
              ‖kappa / (r : ℂ) *
                ModifiedBessel.K2 (kappa * (r : ℂ))‖ := norm_add_le _ _
          _ = _ := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ ‖kappa‖ ^ 2 * (E * C1) + ‖kappa‖ * (E * C2) := by
        gcongr
      _ = E * K1SecondDerivativeConstant kappa := by
        simp only [K1SecondDerivativeConstant, C1, C2]
        ring
  · rw [deriv_deriv_K2_realRadial hkappa hrpos]
    change ‖(kappa ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)) +
        kappa / (r : ℂ) * ModifiedBessel.K1 (kappa * (r : ℂ))) +
        6 / (r : ℂ) ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ))‖ ≤
      E * K2SecondDerivativeConstant kappa
    calc
      _ ≤
          ‖kappa ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ)) +
            kappa / (r : ℂ) * ModifiedBessel.K1 (kappa * (r : ℂ))‖ +
          ‖6 / (r : ℂ) ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ))‖ :=
        norm_add_le _ _
      _ ≤
          (‖kappa‖ ^ 2 * ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ +
            ‖kappa / (r : ℂ)‖ *
              ‖ModifiedBessel.K1 (kappa * (r : ℂ))‖) +
          ‖(6 : ℂ) / (r : ℂ) ^ 2‖ *
            ‖ModifiedBessel.K2 (kappa * (r : ℂ))‖ := by
        apply add_le_add
        · calc
            _ ≤ ‖kappa ^ 2 * ModifiedBessel.K2 (kappa * (r : ℂ))‖ +
                ‖kappa / (r : ℂ) *
                  ModifiedBessel.K1 (kappa * (r : ℂ))‖ := norm_add_le _ _
            _ = _ := by rw [norm_mul, norm_mul, norm_pow]
        · rw [norm_mul]
      _ ≤ (‖kappa‖ ^ 2 * (E * C2) + ‖kappa‖ * (E * C1)) +
          6 * (E * C2) := by gcongr
      _ = E * K2SecondDerivativeConstant kappa := by
        simp only [K2SecondDerivativeConstant, C1, C2]
        ring

/-! ## Cross-normalized exponential bounds -/

/-- Exponential-envelope constant for the second derivative of the exterior plus branch. -/
def plusSecondDerivativeConstant (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I2 kappa‖ * K2SecondDerivativeConstant kappa

/-- Exponential-envelope constant for the second derivative of the exterior minus branch. -/
def minusSecondDerivativeConstant (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I0 kappa‖ * K0SecondDerivativeConstant kappa

/-- Exponential-envelope constant for the second derivative of the exterior axial branch. -/
def axialSecondDerivativeConstant (N : ℝ) (kappa : ℂ) : ℝ :=
  ‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
    K1SecondDerivativeConstant kappa

/-- Simultaneous exponential bounds for the second derivatives of the three
cross-normalized exterior radial branches. -/
theorem exterior_branch_secondDerivative_exponential_bounds
    (N : ℝ) {kappa : ℂ} (hkappa : 0 < kappa.re) {r : ℝ} (hr : 1 ≤ r) :
    ‖deriv (deriv (plusOutsideReal kappa)) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) * plusSecondDerivativeConstant kappa ∧
      ‖deriv (deriv (minusOutsideReal kappa)) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) * minusSecondDerivativeConstant kappa ∧
      ‖deriv (deriv (axialOutsideReal N kappa)) r‖ ≤
        Real.exp (-kappa.re * (r - 1)) * axialSecondDerivativeConstant N kappa := by
  obtain ⟨h0, h1, h2⟩ :=
    modifiedBessel_K012_realRadial_secondDerivative_exponential_bounds hkappa hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  constructor
  · rw [deriv_deriv_plusOutsideReal hkappa hrpos,
      ← deriv_deriv_K2_realRadial hkappa hrpos, norm_mul]
    calc
      _ ≤ ‖ModifiedBessel.I2 kappa‖ *
          (Real.exp (-kappa.re * (r - 1)) * K2SecondDerivativeConstant kappa) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = _ := by simp [plusSecondDerivativeConstant]; ring
  constructor
  · rw [deriv_deriv_minusOutsideReal hkappa hrpos,
      ← deriv_deriv_K0_realRadial hkappa hrpos, norm_mul, norm_neg]
    calc
      _ ≤ ‖ModifiedBessel.I0 kappa‖ *
          (Real.exp (-kappa.re * (r - 1)) * K0SecondDerivativeConstant kappa) :=
        mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
      _ = _ := by simp [minusSecondDerivativeConstant]; ring
  · rw [deriv_deriv_axialOutsideReal N hkappa hrpos]
    have heq :
        ‖-(ModifiedBessel.I1 kappa *
            deriv (deriv (fun s : ℝ ↦
              ModifiedBessel.K1 (kappa * (s : ℂ)))) r) /
            (I * (N : ℂ))‖ =
          ‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
            ‖deriv (deriv (fun s : ℝ ↦
              ModifiedBessel.K1 (kappa * (s : ℂ)))) r‖ := by
      rw [norm_div, norm_neg, norm_mul, norm_div]
      ring
    rw [show kappa ^ 2 * ModifiedBessel.K1 (kappa * (r : ℂ)) +
        kappa / (r : ℂ) * ModifiedBessel.K2 (kappa * (r : ℂ)) =
          deriv (deriv (fun s : ℝ ↦
            ModifiedBessel.K1 (kappa * (s : ℂ)))) r by
      exact (deriv_deriv_K1_realRadial hkappa hrpos).symm]
    rw [heq]
    calc
      _ ≤ ‖ModifiedBessel.I1 kappa / (I * (N : ℂ))‖ *
          (Real.exp (-kappa.re * (r - 1)) * K1SecondDerivativeConstant kappa) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by simp [axialSecondDerivativeConstant]; ring

end PonomarenkoCartesianExteriorSecondDerivative
end FastDynamo

/-!
## Smoothness of the scalar exterior ingredients

The complex radius and the exterior phase `(y₁ + i y₂) / ‖y‖` are smooth away from the origin.
-/

noncomputable section

namespace FastDynamo
namespace PonomarenkoExteriorSecondDerivative

open Complex Filter Metric MeasureTheory Set Topology
open CartesianRadialRegularity
open PonomarenkoCrossNormalizedJump
open PonomarenkoCrossNormalizedAxial
open ComplexRadius
open PonomarenkoCartesianExteriorDerivative
open PonomarenkoCartesianExteriorSecondDerivative

/-- The complex radius is smooth at every nonzero point. -/
theorem complexRadius_contDiffAt_infty
    {y : WholePlane} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) complexRadius y := by
  have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ ‖x‖) y :=
    contDiffAt_norm ℝ hy
  have hofReal : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℝ ↦ (r : ℂ)) ‖y‖ :=
    Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun x : WholePlane ↦ ((‖x‖ : ℝ) : ℂ)) y
  exact ContDiffAt.fun_comp y (g := fun r : ℝ ↦ (r : ℂ)) hofReal hnorm

/-- The exterior phase is smooth at every nonzero point. -/
theorem exteriorPhase_contDiffAt_infty
    {y : WholePlane} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) exteriorPhase y := by
  have hcoordinate : ContDiffAt ℝ (⊤ : ℕ∞) complexCoordinate y :=
    complexCoordinate_contDiff.contDiffAt.of_le (by simp)
  have hradius : ContDiffAt ℝ (⊤ : ℕ∞) complexRadius y :=
    complexRadius_contDiffAt_infty hy
  have hradius0 : complexRadius y ≠ 0 := by
    exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have h : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : WholePlane ↦ complexCoordinate x * (complexRadius x)⁻¹) y :=
    hcoordinate.mul (hradius.inv hradius0)
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun x : WholePlane ↦ complexCoordinate x * (complexRadius x)⁻¹) y
  exact h

end PonomarenkoExteriorSecondDerivative
end FastDynamo

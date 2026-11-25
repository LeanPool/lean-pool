/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RadialPoissonSlope
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RadialCumulativeSign

/-!
# The radial Poisson primitive

The radial Poisson slope can be integrated from a positive reference radius.
On the positive half-line, the resulting primitive has the prescribed first
derivative and satisfies the radial Poisson equation.  For the explicit
difference of two kernel scales, the primitive is nonnegative before the
larger support radius and vanishes after it.

No regularity at the origin is asserted in this file.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval Topology

namespace SGPT.Foundations.Analysis.Pending.RadialPoissonPrimitive

open RadialPoissonCertificate
open RadialPoissonSlope
open RadialCumulativeSign
open RadialPolarMass

/-- The radial Poisson primitive, normalized to vanish at the reference
squared radius `A`. -/
noncomputable def radialPoissonPrimitive
    (n : ℕ) (g : ℝ → ℝ) (A s : ℝ) : ℝ :=
  ∫ t in A..s, radialPoissonSlope n g t

@[simp]
theorem radialPoissonPrimitive_self
    (n : ℕ) (g : ℝ → ℝ) (A : ℝ) :
    radialPoissonPrimitive n g A A = 0 := by
  simp [radialPoissonPrimitive]

/-- The radial Poisson slope is continuous on the positive half-line. -/
theorem radialPoissonSlope_continuousOn_Ioi
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (radialPoissonSlope n g) (Ioi 0) := by
  intro s hs
  exact (radialPoissonSlope_hasDerivAt hn hg hs).continuousAt.continuousWithinAt

/-- On the positive half-line, differentiating the primitive recovers the
radial Poisson slope. -/
theorem radialPoissonPrimitive_hasDerivAt
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    HasDerivAt (radialPoissonPrimitive n g A)
      (radialPoissonSlope n g s) s := by
  have hsub : uIcc A s ⊆ Ioi (0 : ℝ) := by
    simp [uIcc, Icc_subset_Ioi_iff, hA, hs]
  have hcont := radialPoissonSlope_continuousOn_Ioi hn hg
  have hint : IntervalIntegrable (radialPoissonSlope n g) volume A s :=
    (hcont.mono hsub).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (radialPoissonSlope n g) (𝓝 s) :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi s hs
  have hconts : ContinuousAt (radialPoissonSlope n g) s :=
    isOpen_Ioi.continuousOn_iff.mp hcont hs
  unfold radialPoissonPrimitive
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hconts

/-- The derivative of the primitive is itself differentiable away from the
origin, with the quotient-rule derivative of the radial slope. -/
theorem radialPoissonPrimitive_deriv_hasDerivAt
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    HasDerivAt (deriv (radialPoissonPrimitive n g A))
      (g s / (4 * s) -
        (n : ℝ) * radialPoissonSlope n g s / s) s := by
  apply (radialPoissonSlope_hasDerivAt hn hg hs).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact (radialPoissonPrimitive_hasDerivAt hn hg hA ht).deriv

/-- The radial primitive satisfies the second-order one-variable Poisson
equation on the positive half-line. -/
theorem radialPoissonPrimitive_ode
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    4 * (s * deriv (deriv (radialPoissonPrimitive n g A)) s +
      (n : ℝ) * deriv (radialPoissonPrimitive n g A) s) = g s := by
  rw [(radialPoissonPrimitive_deriv_hasDerivAt hn hg hA hs).deriv,
    (radialPoissonPrimitive_hasDerivAt hn hg hA hs).deriv]
  field_simp
  ring

/-- If the radial slope is nonpositive between `s` and the normalization
radius `A`, then the primitive is nonnegative at `s`. -/
theorem radialPoissonPrimitive_nonneg
    {n : ℕ} {g : ℝ → ℝ} {A s : ℝ} (hsA : s ≤ A)
    (hslope : ∀ t ∈ Icc s A, radialPoissonSlope n g t ≤ 0) :
    0 ≤ radialPoissonPrimitive n g A s := by
  calc
    radialPoissonPrimitive n g A s =
        ∫ t in s..A, -radialPoissonSlope n g t := by
      rw [radialPoissonPrimitive, intervalIntegral.integral_symm,
        intervalIntegral.integral_neg]
    _ ≥ 0 := intervalIntegral.integral_nonneg hsA fun t ht =>
      neg_nonneg.mpr (hslope t ht)

/-- If the slope vanishes at and beyond the normalization radius, then the
primitive vanishes there as well. -/
theorem radialPoissonPrimitive_eq_zero_of_slope_eq_zero
    {n : ℕ} {g : ℝ → ℝ} {A s : ℝ} (hAs : A ≤ s)
    (hzero : ∀ t, A ≤ t → radialPoissonSlope n g t = 0) :
    radialPoissonPrimitive n g A s = 0 := by
  unfold radialPoissonPrimitive
  calc
    (∫ t in A..s, radialPoissonSlope n g t) = ∫ _t in A..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc A s := (uIcc_of_le hAs).symm ▸ ht
      exact hzero t ht'.1
    _ = 0 := by simp

/-- If a weighted radial datum is integrable on the positive half-line, has
zero total weighted mass, and vanishes after `A`, then its weighted cumulative
term vanishes at every `s ≥ A`. -/
theorem radialWeightedCumulative_eq_zero_of_total_and_outer_zero
    {n : ℕ} {g : ℝ → ℝ} {A s : ℝ} (hA : 0 < A) (hAs : A ≤ s)
    (hint : IntegrableOn (fun t : ℝ => t ^ (n - 1) * g t) (Ioi 0))
    (htotal : ∫ t in Ioi (0 : ℝ), t ^ (n - 1) * g t = 0)
    (hzero : ∀ t, A < t → g t = 0) :
    radialWeightedCumulative n g s = 0 := by
  let f : ℝ → ℝ := fun t => t ^ (n - 1) * g t
  have hs : 0 ≤ s := hA.le.trans hAs
  have hintS : IntegrableOn f (Ioi s) :=
    hint.mono_set (Ioi_subset_Ioi hs)
  have htail : ∫ t in Ioi s, f t = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    dsimp [f]
    rw [hzero t (hAs.trans_lt ht), mul_zero]
  have hadd := intervalIntegral.integral_interval_add_Ioi
    (a := (0 : ℝ)) (b := s) hint hintS
  rw [htail, add_zero, htotal] at hadd
  rw [radialWeightedCumulative]
  exact hadd

/-- The explicit kernel difference has a nonpositive Poisson slope whenever
the scale index increases. -/
theorem radialPoissonSlope_explicitRadialKernelSqDifference_nonpos
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ} (hs : 0 < s) :
    radialPoissonSlope n
      (explicitRadialKernelSqDifference (n := n) R hR a b) s ≤ 0 :=
  radialPoissonSlope_nonpos hs
    (radialWeightedCumulative_explicitRadialKernelSqDifference_nonpos
      hn R hR hab hs.le)

/-- Before the normalization radius, the primitive associated to an
increasing pair of kernel scales is nonnegative. -/
theorem radialPoissonPrimitive_explicitRadialKernelSqDifference_nonneg
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {A s : ℝ}
    (hs : 0 < s) (hsA : s ≤ A) :
    0 ≤ radialPoissonPrimitive n
      (explicitRadialKernelSqDifference (n := n) R hR a b) A s := by
  apply radialPoissonPrimitive_nonneg hsA
  intro t ht
  exact radialPoissonSlope_explicitRadialKernelSqDifference_nonpos
    hn R hR hab (hs.trans_le ht.1)

/-- The weighted cumulative term of the explicit kernel difference vanishes
at and beyond the squared outer radius of the larger-support scale. -/
theorem radialWeightedCumulative_explicitRadialKernelSqDifference_eq_zero_of_outer
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ}
    (hs : (R / ((a : ℝ) + 1)) ^ 2 ≤ s) :
    radialWeightedCumulative n
      (explicitRadialKernelSqDifference (n := n) R hR a b) s = 0 := by
  let A : ℝ := (R / ((a : ℝ) + 1)) ^ 2
  let g : ℝ → ℝ :=
    explicitRadialKernelSqDifference (n := n) R hR a b
  let f : ℝ → ℝ := fun t => t ^ (n - 1) * g t
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hfcont : Continuous f :=
    (continuous_id.pow _).mul
      (explicitRadialKernelSqDifference_contDiff R hR a b).continuous
  have hleft : IntegrableOn f (Ioc 0 A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mp
      (hfcont.intervalIntegrable 0 A)
  have hright : IntegrableOn f (Ioi A) := by
    apply integrableOn_zero.congr_fun
    · intro t ht
      dsimp [f, g]
      rw [explicitRadialKernelSqDifference_eq_zero_of_sq_rOut_le
        R hR hab ht.le, mul_zero]
    · exact measurableSet_Ioi
  have hint : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hA.le]
    exact hleft.union hright
  apply radialWeightedCumulative_eq_zero_of_total_and_outer_zero
    hA hs hint
  · exact integral_explicitRadialKernelSqDifference_weighted_eq_zero
      hn R hR a b
  · intro t ht
    exact explicitRadialKernelSqDifference_eq_zero_of_sq_rOut_le
      R hR hab ht.le

/-- The explicit Poisson slope vanishes at and beyond the squared outer
radius of the larger-support scale. -/
theorem radialPoissonSlope_explicitRadialKernelSqDifference_eq_zero_of_outer
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ}
    (hs : (R / ((a : ℝ) + 1)) ^ 2 ≤ s) :
    radialPoissonSlope n
      (explicitRadialKernelSqDifference (n := n) R hR a b) s = 0 := by
  rw [radialPoissonSlope,
    radialWeightedCumulative_explicitRadialKernelSqDifference_eq_zero_of_outer
      hn R hR hab hs,
    zero_div]

/-- With the reference point chosen at the exact squared outer radius, the
explicit primitive vanishes everywhere outside that radius. -/
theorem radialPoissonPrimitive_explicitRadialKernelSqDifference_eq_zero_of_outer
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    {a b : ℕ} (hab : a ≤ b) {s : ℝ}
    (hs : (R / ((a : ℝ) + 1)) ^ 2 ≤ s) :
    radialPoissonPrimitive n
      (explicitRadialKernelSqDifference (n := n) R hR a b)
      ((R / ((a : ℝ) + 1)) ^ 2) s = 0 := by
  apply radialPoissonPrimitive_eq_zero_of_slope_eq_zero hs
  intro t ht
  exact radialPoissonSlope_explicitRadialKernelSqDifference_eq_zero_of_outer
    hn R hR hab ht

end SGPT.Foundations.Analysis.Pending.RadialPoissonPrimitive

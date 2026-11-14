/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Fourier.LpSpace
public import LeanPool.LiebThirring.Defs.Configuration
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Low Fourier cutoff fields

The Fourier kinetic multiplier with the normalization.

The closed low momentum region at real energy `E`.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal

namespace LiebThirring

/-- The Fourier kinetic multiplier with the normalization. -/
@[expose] noncomputable def fourierKineticMultiplier (ξ : Position) : ℝ :=
  (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

/-- The closed low momentum region at real energy `E`. -/
@[expose] noncomputable def lowMomentumRegion (E : ℝ) : Set Position :=
  {ξ | fourierKineticMultiplier ξ ≤ E}

theorem continuous_fourierKineticMultiplier : Continuous fourierKineticMultiplier := by
  unfold fourierKineticMultiplier
  fun_prop

theorem measurableSet_lowMomentumRegion (E : ℝ) : MeasurableSet (lowMomentumRegion E) :=
  measurableSet_le continuous_fourierKineticMultiplier.measurable measurable_const

/-- The low region is exactly the ball of radius `sqrt E / (2π)`. -/
theorem lowMomentumRegion_eq_closedBall (E : ℝ) (hE : 0 ≤ E) :
    lowMomentumRegion E = Metric.closedBall 0 (Real.sqrt E / (2 * Real.pi)) := by
  ext ξ
  simp only [lowMomentumRegion, fourierKineticMultiplier, Set.mem_ofPred_eq,
    Metric.mem_closedBall, dist_zero_right]
  rw [le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
  have hs := Real.sq_sqrt hE
  have hn := norm_nonneg ξ
  have hsn := Real.sqrt_nonneg E
  have hprod : 0 ≤ ‖ξ‖ * (2 * Real.pi) := mul_nonneg hn (by positivity)
  rw [← sq_le_sq₀ hprod hsn]
  rw [hs]
  ring_nf

/-- Every low momentum region at nonnegative energy has finite volume. -/
theorem volume_lowMomentumRegion_ne_top (E : ℝ) (hE : 0 ≤ E) :
    volume (lowMomentumRegion E) ≠ ⊤ := by
  rw [lowMomentumRegion_eq_closedBall E hE, EuclideanSpace.volume_closedBall_fin_three]
  finiteness

/-- Exact three-dimensional phase-space volume, including `E = 0`. -/
theorem volume_lowMomentumRegion (E : ℝ) (hE : 0 ≤ E) :
    volume (lowMomentumRegion E) = ENNReal.ofReal ((1 / (6 * Real.pi ^ 2)) * E ^ ((3 : ℝ) / 2)) :=
      by
  rw [lowMomentumRegion_eq_closedBall E hE, EuclideanSpace.volume_closedBall_fin_three,
    ← ENNReal.ofReal_pow (div_nonneg (Real.sqrt_nonneg E) (by positivity)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_div_two_eq_sqrt 3 hE]
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  field_simp
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The same raw inverse Fourier integral is used for every real energy and point. -/
@[expose] noncomputable def lowFourierField (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (x : Position) : H :=
  𝓕⁻ ((lowMomentumRegion E).indicator
    (Lp.fourierTransformₗᵢ Position H h : Position → H)) x

/-- The supported Fourier representative is integrable, with no finite-energy premise. -/
theorem integrable_lowFourierRepresentative (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (hE : 0 ≤ E) :
    Integrable ((lowMomentumRegion E).indicator
      (Lp.fourierTransformₗᵢ Position H h : Position → H)) :=
  (integrable_indicator_iff (measurableSet_lowMomentumRegion E)).mpr
    (integrableOn_Lp_of_measure_ne_top (Lp.fourierTransformₗᵢ Position H h)
    (by norm_num) (volume_lowMomentumRegion_ne_top E hE))

/-- Each inverse Fourier integrand defining the low field is Bochner integrable. -/
theorem integrable_lowFourierField (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (hE : 0 ≤ E) (x : Position) :
    Integrable (fun ξ : Position => Real.fourierChar (inner ℝ ξ x) •
      (lowMomentumRegion E).indicator
        (Lp.fourierTransformₗᵢ Position H h : Position → H) ξ) := by
  simpa only [inner_neg_right, neg_neg] using
    (Real.fourierIntegral_convergent_iff (-x)).mpr
      (integrable_lowFourierRepresentative h E hE)

/-- The defining integral has the positive inverse Fourier phase from Fourier cutoff. -/
theorem lowFourierField_eq_integral (h : Lp H 2 (volume : Measure Position))
    (E : ℝ) (x : Position) :
    lowFourierField h E x = ∫ ξ in lowMomentumRegion E,
      Real.fourierChar (inner ℝ ξ x) • (Lp.fourierTransformₗᵢ Position H h) ξ := by
  rw [lowFourierField, Real.fourierInv_eq, ← integral_indicator
    (measurableSet_lowMomentumRegion E)]
  apply integral_congr_ae
  filter_upwards with ξ
  by_cases hξ : ξ ∈ lowMomentumRegion E
  · simp only [Set.indicator_of_mem hξ]
  · simp only [Set.indicator_of_notMem hξ, smul_zero]

/-- One fixed Fourier representative gives joint strong measurability for all energies. -/
theorem stronglyMeasurable_lowFourierField (h : Lp H 2 (volume : Measure Position)) :
    StronglyMeasurable (fun p : ℝ × Position => lowFourierField h p.1 p.2) := by
  let A : Set ((ℝ × Position) × Position) :=
    {p | fourierKineticMultiplier p.2 ≤ p.1.1}
  have hA : MeasurableSet A := measurableSet_le
    (continuous_fourierKineticMultiplier.measurable.comp measurable_snd)
    (measurable_fst.comp measurable_fst)
  have hc : Continuous (fun p : (ℝ × Position) × Position =>
      Real.fourierChar (inner ℝ p.2 p.1.2)) := by
    fun_prop
  have hf := (Lp.stronglyMeasurable (Lp.fourierTransformₗᵢ Position H h)).comp_measurable
    (measurable_snd : Measurable (Prod.snd : (ℝ × Position) × Position → Position))
  have hi := (hc.stronglyMeasurable.smul hf).indicator hA
  have hm := hi.integral_prod_right' (ν := (volume : Measure Position))
  have heq : (fun p : ℝ × Position => lowFourierField h p.1 p.2) =
      (fun p : ℝ × Position => ∫ ξ, A.indicator
        (fun z => Real.fourierChar (inner ℝ z.2 z.1.2) •
          (Lp.fourierTransformₗᵢ Position H h) z.2) (p, ξ)) := by
    funext p
    rw [lowFourierField_eq_integral, ← integral_indicator
      (measurableSet_lowMomentumRegion p.1)]
    apply integral_congr_ae
    filter_upwards with ξ
    by_cases hξ : ξ ∈ lowMomentumRegion p.1
    · have hz : (p, ξ) ∈ A := hξ
      simp only [Set.indicator_of_mem hξ, Set.indicator_of_mem hz]
    · have hz : (p, ξ) ∉ A := hξ
      simp only [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hz]
  rw [heq]
  exact hm

/-- Subtracting the low integral from any fixed strongly measurable representative
preserves joint strong measurability. -/
theorem stronglyMeasurable_highFourierField (h : Lp H 2 (volume : Measure Position))
    (f : Position → H) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun p : ℝ × Position => f p.2 - lowFourierField h p.1 p.2) :=
  (hf.comp_measurable measurable_snd).sub (stronglyMeasurable_lowFourierField h)

end LiebThirring
end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalEhrhard
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Gaussian-CDF distance approximations of compact sets -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology Pointwise

namespace EhrhardGaussian.Ehrhard

/-- The distance quantile subtracts a multiple of the distance to a set from a fixed height. -/
def distanceQuantile {n : ℕ} (A : Set (Fin n → ℝ)) (m k : ℝ) (x : Fin n → ℝ) : ℝ :=
  m - k * infDist x A

/-- The distance quantile is continuous. -/
theorem continuous_distanceQuantile {n : ℕ} (A : Set (Fin n → ℝ)) (m k : ℝ) :
    Continuous (distanceQuantile A m k) := continuous_const.sub (continuous_const.mul
      (continuous_infDist_pt A))

/-- A distance quantile with nonnegative slope is bounded above by its height. -/
theorem distanceQuantile_le {n : ℕ} (A : Set (Fin n → ℝ)) (m : ℝ) {k : ℝ} (hk : 0 ≤ k) (x) :
    distanceQuantile A m k x ≤ m := sub_le_self _ (mul_nonneg hk infDist_nonneg)

/-- A positive-slope distance quantile of a nonempty compact set tends to minus infinity at spatial
infinity. -/
theorem tendsto_distanceQuantile_atBot {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hAne : A.Nonempty) (m : ℝ) {k : ℝ} (hk : 0 < k) :
    Tendsto (distanceQuantile A m k) (cocompact (Fin n → ℝ)) atBot := by
  obtain ⟨a, ha⟩ := hAne
  have hnorm (x : Fin n → ℝ) : ‖x‖ ≤ infDist x A + diam A + ‖a‖ := by
    have hdist := dist_le_infDist_add_diam hA.isBounded ha (x := x)
    calc
      _ = ‖(x - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
      _ = dist x a + ‖a‖ := by rw [dist_eq_norm]
      _ ≤ _ := by linarith only [hdist]
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
    (eventually_ge_atTop ((m - b) / k + diam A + ‖a‖))] with x hx
  have hd : (m - b) / k ≤ infDist x A := by linarith only [hx, hnorm x]
  have hmul := (div_le_iff₀ hk).mp hd
  dsimp only [distanceQuantile]
  nlinarith only [hmul]

/-- Distance to a weighted sum of compact sets is bounded by the weighted distances to the two sets.
-/
theorem infDist_minkowski_le {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (x y : Fin n → ℝ) :
    infDist (p • x + q • y) (p • A + q • B) ≤ p * infDist x A + q * infDist y B := by
  obtain ⟨a, ha, hda⟩ := hA.exists_infDist_eq_dist hAne x
  obtain ⟨b, hb, hdb⟩ := hB.exists_infDist_eq_dist hBne y
  have hmem : p • a + q • b ∈ p • A + q • B :=
    Set.add_mem_add (Set.smul_mem_smul_set ha) (Set.smul_mem_smul_set hb)
  calc
    _ ≤ dist (p • x + q • y) (p • a + q • b) := infDist_le_dist_of_mem hmem
    _ = ‖p • (x - a) + q • (y - b)‖ := by rw [dist_eq_norm]; congr 1; module
    _ ≤ ‖p • (x - a)‖ + ‖q • (y - b)‖ := norm_add_le _ _
    _ = p * infDist x A + q * infDist y B := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg
        hq,
        hda, hdb, dist_eq_norm, dist_eq_norm]

/-- Distance quantiles satisfy the pointwise comparison for weighted sums of compact sets. -/
theorem distanceQuantile_minkowski {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q = 1) (m : ℝ) {k : ℝ} (hk : 0 ≤ k)
    (x y : Fin n → ℝ) :
    p * distanceQuantile A m k x + q * distanceQuantile B m k y ≤
      distanceQuantile (p • A + q • B) m k (p • x + q • y) := by
  have h := mul_le_mul_of_nonneg_left (infDist_minkowski_le hA hB hAne hBne hp hq x y) hk
  have hm : p * m + q * m = m := by rw [← add_mul, hsum, one_mul]
  dsimp only [distanceQuantile]
  nlinarith only [h, hm]

/-- Increasing the distance penalty makes its Gaussian probability converge to a constant multiple
of the set indicator. -/
theorem tendsto_distance_probability {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : IsClosed A) (hAne : A.Nonempty) (m : ℝ) (x : Fin n → ℝ) :
    Tendsto (fun j : ℕ => gaussianCDF (distanceQuantile A m ((j : ℝ) + 1) x)) atTop
      (𝓝 (A.indicator (fun _ => gaussianCDF m) x)) := by
  by_cases hx : x ∈ A
  · simp only [distanceQuantile, infDist_zero_of_mem hx, mul_zero, sub_zero, indicator_of_mem hx]
    exact tendsto_const_nhds
  · have hd : 0 < infDist x A := (hA.notMem_iff_infDist_pos hAne).mp hx
    have htop : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * infDist x A) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const hd
    have hbot := tendsto_atBot_add_const_left atTop m (tendsto_neg_atTop_atBot.comp htop)
    have hPhi : Tendsto gaussianCDF atBot (𝓝 0) := tendsto_cdf_atBot (gaussianReal 0 1)
    simpa only [distanceQuantile, sub_eq_add_neg, indicator_of_notMem hx, Function.comp_def] using
      hPhi.comp hbot

/-- The Gaussian means of distance probabilities converge to the corresponding compact-set
probability times the height factor. -/
theorem tendsto_integral_distance_probability {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hAne : A.Nonempty) (m : ℝ) :
    Tendsto (fun j : ℕ => ∫ x, gaussianCDF (distanceQuantile A m ((j : ℝ) + 1) x)
      ∂standardGaussianMeasure n)
      atTop (𝓝 (gaussianCDF m * (standardGaussianMeasure n A).toReal)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := standardGaussianMeasure n)
    (l := (atTop : Filter ℕ)) (F := fun j x => gaussianCDF (distanceQuantile A m ((j : ℝ) + 1) x))
    (f := A.indicator (fun _ => gaussianCDF m)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun j => (continuous_gaussianCDF.comp (continuous_distanceQuantile A m
      _)).aestronglyMeasurable)
    (Eventually.of_forall fun j => ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (gaussianCDF_pos _)] using (gaussianCDF_lt_one
        (distanceQuantile A m ((j : ℝ) + 1) x)).le)
    (integrable_const 1) (ae_of_all _ fun x => tendsto_distance_probability hA.isClosed hAne m x)
  simpa only [integral_indicator hA.measurableSet, setIntegral_const, Measure.real, smul_eq_mul,
    mul_comm] using h

end EhrhardGaussian.Ehrhard

end

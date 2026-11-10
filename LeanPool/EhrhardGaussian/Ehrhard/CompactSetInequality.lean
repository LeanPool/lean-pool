/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.DistanceApproximation
public import LeanPool.EhrhardGaussian.Ehrhard.FunctionalThresholds

/-! # Ehrhard's inequality for compact sets under the standard Gaussian -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology Pointwise

namespace EhrhardGaussian.Ehrhard

/-- Strict lower bounds on two compact-set Gaussian probabilities imply the Ehrhard bound for their
weighted sum. -/
theorem compact_set_ehrhard_strict {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) {a b : ℝ}
    (ha : gaussianCDF a < (standardGaussianMeasure n A).toReal)
    (hb : gaussianCDF b < (standardGaussianMeasure n B).toReal) :
    gaussianCDF (p * a + q * b) ≤ (standardGaussianMeasure n (p • A + q • B)).toReal := by
  let C := p • A + q • B
  have hC : IsCompact C := (hA.smul p).add (hB.smul q)
  obtain ⟨x, hx⟩ := hAne
  obtain ⟨y, hy⟩ := hBne
  have hCne : C.Nonempty := ⟨p • x + q • y, Set.add_mem_add (Set.smul_mem_smul_set hx)
    (Set.smul_mem_smul_set hy)⟩
  have hPhi : Tendsto gaussianCDF atTop (𝓝 1) := tendsto_cdf_atTop (gaussianReal 0 1)
  have hma := hPhi.mul_const (standardGaussianMeasure n A).toReal
  have hmb := hPhi.mul_const (standardGaussianMeasure n B).toReal
  simp only [one_mul] at hma hmb
  obtain ⟨m, hma, hmb⟩ := ((hma.eventually (lt_mem_nhds ha)).and (hmb.eventually (lt_mem_nhds
    hb))).exists
  have hAlim := tendsto_integral_distance_probability hA ⟨x, hx⟩ m
  have hBlim := tendsto_integral_distance_probability hB ⟨y, hy⟩ m
  have hClim := tendsto_integral_distance_probability hC hCne m
  have hcomp : ∀ᶠ j : ℕ in atTop,
      gaussianCDF (p * a + q * b) ≤ ∫ z, gaussianCDF (distanceQuantile C m ((j : ℝ) + 1) z)
        ∂standardGaussianMeasure n := by
    filter_upwards [hAlim.eventually (lt_mem_nhds hma), hBlim.eventually (lt_mem_nhds hmb)] with j
      hjA hjB
    have hk : 0 < (j : ℝ) + 1 := by positivity
    exact functional_ehrhard_thresholds (continuous_distanceQuantile A m _)
      (continuous_distanceQuantile B m _)
      (continuous_distanceQuantile C m _) (tendsto_distanceQuantile_atBot hA ⟨x, hx⟩ m hk)
      (tendsto_distanceQuantile_atBot hB ⟨y, hy⟩ m hk) (tendsto_distanceQuantile_atBot hC hCne m hk)
      hp hq hsum (distanceQuantile_le A m hk.le) (distanceQuantile_le B m hk.le)
      (distanceQuantile_minkowski hA hB ⟨x, hx⟩ ⟨y, hy⟩ hp.le hq.le hsum m hk.le) hjA.le hjB.le
  have h := ge_of_tendsto hClim hcomp
  exact h.trans ((mul_le_mul_of_nonneg_right (gaussianCDF_lt_one m).le
    ENNReal.toReal_nonneg).trans_eq (one_mul _))

/-- Compact sets satisfy the Gaussian Ehrhard inequality for positive convex weights. -/
theorem compact_set_ehrhard {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) {a b : ℝ}
    (ha : gaussianCDF a ≤ (standardGaussianMeasure n A).toReal)
    (hb : gaussianCDF b ≤ (standardGaussianMeasure n B).toReal) :
    gaussianCDF (p * a + q * b) ≤ (standardGaussianMeasure n (p • A + q • B)).toReal := by
  let ε := fun j : ℕ => 1 / ((j : ℝ) + 1)
  have hε (j) : 0 < ε j := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomp (j) := compact_set_ehrhard_strict hA hB hAne hBne hp hq hsum
    ((strictMono_gaussianCDF (sub_lt_self a (hε j))).trans_le ha)
    ((strictMono_gaussianCDF (sub_lt_self b (hε j))).trans_le hb)
  have halim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).sub hεlim
  have hblim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).sub hεlim
  have hlim := continuous_gaussianCDF.continuousAt.tendsto.comp ((halim.const_mul p).add
    (hblim.const_mul q))
  have h := le_of_tendsto hlim (Eventually.of_forall hcomp)
  simpa only [sub_zero] using h

end EhrhardGaussian.Ehrhard

end

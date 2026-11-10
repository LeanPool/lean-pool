/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.SmoothTripleComparison
public import LeanPool.EhrhardGaussian.Ehrhard.ScalarApproximationSequence

/-! # The functional comparison for continuous triples constant outside compact sets -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)
open scoped Topology ContDiff

namespace EhrhardGaussian.Ehrhard

/-- A strict pointwise quantile comparison for three continuous profiles passes to their correlated
Gaussian means. -/
theorem continuous_triple_quantile_comparison {f : Fin 3 → ℝ → ℝ}
    (hf : ∀ i, Continuous (f i)) (c : Fin 3 → ℝ)
    (hcompact : ∀ i, HasCompactSupport (fun y => f i y - c i))
    {lo hi p q ρ σ η : ℝ} (hlo : 0 < lo) (hhi : hi < 1)
    (hbound : ∀ i z, f i z ∈ Icc lo hi) (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (hρ : |ρ| < 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (hη : 0 < η) (hgap : ∀ y : Fin 2 → ℝ,
      quantileLinear (tripleTheta p q σ) (fun i => tripleLift f p q ρ i y) ≤ -η) :
    quantileLinear (tripleTheta p q σ)
      (fun i => ∫ y, tripleLift f p q ρ i y ∂standardGaussianMeasure 2) ≤ 0 := by
  let θ := tripleTheta p q σ
  obtain ⟨g, hgsmooth, hgcompact, hgclose, hglimit⟩ := exists_scalar_approximation_sequence hf c
    hcompact
  obtain ⟨δ, hδ, hstable⟩ := exists_quantile_gap_tolerance θ hlo hhi hη
  let ζ := min δ (min (lo / 2) ((1 - hi) / 2))
  have hζ : 0 < ζ := lt_min hδ (lt_min (half_pos hlo) (half_pos (sub_pos.mpr hhi)))
  have hεlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ζ := hεlim.eventually (gt_mem_nhds hζ)
  have hrange (n : ℕ) (hn : 1 / ((n : ℝ) + 1) < ζ) (i) (z) :
      g n i z ∈ Icc (lo / 2) ((hi + 1) / 2) := by
    have he := abs_lt.mp (hgclose n i z)
    have ha : 1 / ((n : ℝ) + 1) < lo / 2 := hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hb : 1 / ((n : ℝ) + 1) < (1 - hi) / 2 := hn.trans_le ((min_le_right _ _).trans
      (min_le_right _ _))
    constructor <;> linarith only [he.1, he.2, (hbound i z).1, (hbound i z).2, ha, hb]
  have hgapg (n : ℕ) (hn : 1 / ((n : ℝ) + 1) < ζ) (y : Fin 2 → ℝ) :
      quantileLinear θ (fun i => tripleLift (g n) p q ρ i y) ≤ -(η / 2) := by
    have h := (hstable (fun i => tripleLift f p q ρ i y) (fun i => tripleLift (g n) p q ρ i y)
      (fun i => hbound i _) (fun i => (hgclose n i _).trans (hn.trans_le (min_le_left _ _))) (hgap
        y)).2
    simpa only [neg_div] using h
  have hcompare : ∀ᶠ n : ℕ in atTop,
      quantileLinear θ (fun i => ∫ y, tripleLift (g n) p q ρ i y ∂standardGaussianMeasure 2) ≤ 0 :=
        by
    filter_upwards [hevent] with n hn
    exact (smooth_triple_quantile_comparison (fun i => (hgsmooth n i).of_le (by simp)) (hgcompact n)
      (half_pos hlo) (by linarith only [hhi]) (hrange n hn) hp hq hsum hρ hσ hvar (half_pos hη)
        (hgapg n hn)).le
  have hmeans : Tendsto (fun n => fun i => ∫ y, tripleLift (g n) p q ρ i y ∂standardGaussianMeasure
    2)
      atTop (𝓝 (fun i => ∫ y, tripleLift f p q ρ i y ∂standardGaussianMeasure 2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => max |lo / 2| |(hi + 1) / 2|)
    · exact Eventually.of_forall fun n =>
        ((hgsmooth n i).continuous.comp (coordinateForm _).continuous).aestronglyMeasurable
    · filter_upwards [hevent] with n hn
      exact ae_of_all _ fun y => by
        simpa only [tripleLift, Function.comp_def, Real.norm_eq_abs] using
          abs_le_max_abs_abs (hrange n hn i _).1 (hrange n hn i _).2
    · exact integrable_const _
    · exact ae_of_all _ fun y => hglimit i (coordinateForm (tripleGaussianFactor p q ρ i) y)
  have hmean : (fun i => ∫ y, tripleLift f p q ρ i y ∂standardGaussianMeasure 2) ∈ probabilityBox :=
    by
    intro i
    have hi := integral_mem_Icc_of_range (standardGaussianMeasure 2)
      ((hf i).comp (coordinateForm (tripleGaussianFactor p q ρ i)).continuous).aestronglyMeasurable
      (fun y => hbound i (coordinateForm (tripleGaussianFactor p q ρ i) y))
    exact ⟨hlo.trans_le hi.1, hi.2.trans_lt hhi⟩
  have hlimit := (contDiffAt_quantileLinear θ hmean).continuousAt.tendsto.comp hmeans
  exact le_of_tendsto hlimit hcompare

end EhrhardGaussian.Ehrhard

end

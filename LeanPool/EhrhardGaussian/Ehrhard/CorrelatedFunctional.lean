/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ClippingLimits

/-! # The correlated scalar functional inequality after removing clipping -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- A pointwise weighted comparison passes to the corresponding quantiles of correlated Gaussian
means. -/
theorem correlated_functional_comparison {u v w : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hutail : Tendsto u (cocompact ℝ) atBot) (hvtail : Tendsto v (cocompact ℝ) atBot)
    (hwtail : Tendsto w (cocompact ℝ) atBot)
    {p q ρ σ U V : ℝ} (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (hρ : |ρ| < 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (huU : ∀ x, u x ≤ U) (hvV : ∀ y, v y ≤ V)
    (horiginal : ∀ x y, p * u x + q * v y ≤ σ * w (p * x + q * y)) :
    quantileLinear (tripleTheta p q σ)
      (fun i => scaledGaussianMean (fun x => gaussianCDF ((![u, v, w] i) x)) (tripleScales σ i)) ≤ 0
        := by
  let N := fun n : ℕ => (n : ℝ) + 1
  let η := fun n : ℕ => 1 / N n
  have hNpos (n) : 0 < N n := by dsimp only [N]; positivity
  have hηpos (n) : 0 < η n := div_pos zero_lt_one (hNpos n)
  have hNlim : Tendsto N atTop atTop := tendsto_atTop_add_const_right atTop 1
    tendsto_natCast_atTop_atTop
  have hηlim : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) := exists_compatible_quantile_cutoffs hp hq hσ U V (N n) (η n) (N n)
  choose H Lf Lg hHN hLfN hLgN hLfU hLgV hH hLf hLg using hex
  have hHlim : Tendsto H atTop atTop := tendsto_atTop_mono hHN hNlim
  have hLflim : Tendsto Lf atTop atTop := tendsto_atTop_mono hLfN hNlim
  have hLglim : Tendsto Lg atTop atTop := tendsto_atTop_mono hLgN hNlim
  have hLH (n) : -N n ≤ H n := by linarith only [hHN n, hNpos n]
  let f : Fin 3 → ℝ → ℝ := fun i x => gaussianCDF ((![u, v, w] i) x)
  let g : ℕ → Fin 3 → ℝ → ℝ := fun n =>
    ![fun x => gaussianCDF (clippedInputQuantile u (Lf n) x),
      fun x => gaussianCDF (clippedInputQuantile v (Lg n) x),
      fun x => gaussianCDF (clippedOutputQuantile w σ (η n) (N n) (H n) x)]
  have hgcont (n) (i) : Continuous (g n i) := by
    fin_cases i
    · exact continuous_gaussianCDF.comp (hu.max continuous_const)
    · exact continuous_gaussianCDF.comp (hv.max continuous_const)
    · exact continuous_gaussianCDF.comp ((hw.add continuous_const).max continuous_const |>.min
      continuous_const)
  have hgrange (n i x) : g n i x ∈ Ioo (0 : ℝ) 1 := by
    fin_cases i <;> exact ⟨gaussianCDF_pos _, gaussianCDF_lt_one _⟩
  have hglimit (i : Fin 3) (x : ℝ) : Tendsto (fun n => g n i x) atTop (𝓝 (f i x)) := by
    fin_cases i
    · exact continuous_gaussianCDF.continuousAt.tendsto.comp (tendsto_clippedInputQuantile hLflim u
      x)
    · exact continuous_gaussianCDF.continuousAt.tendsto.comp (tendsto_clippedInputQuantile hLglim v
      x)
    · exact continuous_gaussianCDF.continuousAt.tendsto.comp
        (tendsto_clippedOutputQuantile hNlim hHlim hηlim (fun n => (hηpos n).le) hσ w x)
  have hcompare (n) : quantileLinear (tripleTheta p q σ)
      (fun i => scaledGaussianMean (g n i) (tripleScales σ i)) ≤ 0 :=
    clipped_scalar_triple_comparison hu hv hw hutail hvtail hwtail hp hq hsum hρ hσ hvar (hηpos n)
      huU hvV horiginal (hLfU n) (hLgV n) (hLH n) (hH n) (hLf n) (hLg n)
  have hmeans : Tendsto (fun n => fun i => scaledGaussianMean (g n i) (tripleScales σ i)) atTop
      (𝓝 (fun i => scaledGaussianMean (f i) (tripleScales σ i))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun n => ((hgcont n i).comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun n => ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, abs_of_pos (hgrange n i _).1] using (hgrange n i _).2.le
    · exact integrable_const 1
    · exact ae_of_all _ fun x => hglimit i (tripleScales σ i * x)
  have hmean : (fun i => scaledGaussianMean (f i) (tripleScales σ i)) ∈ probabilityBox := by
    intro i
    have hcont : Continuous ((![u, v, w] : Fin 3 → ℝ → ℝ) i) := by fin_cases i <;> assumption
    exact integral_gaussianCDF_mem_Ioo (gaussianReal 0 1) (hcont.measurable.comp (by fun_prop))
  have hlimit := (contDiffAt_quantileLinear (tripleTheta p q σ) hmean).continuousAt.tendsto.comp
    hmeans
  exact le_of_tendsto hlimit (Eventually.of_forall hcompare)

end EhrhardGaussian.Ehrhard

end

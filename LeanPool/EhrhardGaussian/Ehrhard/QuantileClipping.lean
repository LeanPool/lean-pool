/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ScalarTripleComparison
public import LeanPool.EhrhardGaussian.Ehrhard.CompatibleClipping

/-! # Compatible clipping and the functional comparison for the clipped inputs -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- The clipped input quantile truncates a scalar function from below at minus the cutoff. -/
def clippedInputQuantile (u : ℝ → ℝ) (L : ℝ) (x : ℝ) : ℝ := max (u x) (-L)

/-- The clipped output quantile shifts a scalar function and truncates it to the prescribed
interval. -/
def clippedOutputQuantile (w : ℝ → ℝ) (σ η L H : ℝ) (x : ℝ) : ℝ :=
  min (max (w x + η / σ) (-L)) H

/-- A bounded input quantile remains between the lower cutoff and its original upper bound. -/
theorem clippedInputQuantile_mem {u : ℝ → ℝ} {L U : ℝ}
    (hu : ∀ x, u x ≤ U) (hLU : -L ≤ U) (x : ℝ) : clippedInputQuantile u L x ∈ Icc (-L) U :=
  ⟨le_max_right _ _, max_le (hu x) hLU⟩

/-- The clipped output quantile lies between its two cutoffs. -/
theorem clippedOutputQuantile_mem (w : ℝ → ℝ) (σ η L H : ℝ) (hLH : -L ≤ H) (x : ℝ) :
    clippedOutputQuantile w σ η L H x ∈ Icc (-L) H :=
  ⟨le_min (le_max_right _ _) hLH, min_le_right _ _⟩

/-- A lower clipped input probability differs from its baseline only on a compact set under decay at
infinity. -/
theorem hasCompactSupport_clippedInput_probability {u : ℝ → ℝ}
    (hu : Tendsto u (cocompact ℝ) atBot) (L : ℝ) :
    HasCompactSupport (fun x => gaussianCDF (clippedInputQuantile u L x) - gaussianCDF (-L)) := by
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
  filter_upwards [hu.eventually (eventually_le_atBot (-L))] with x hx
  simp only [clippedInputQuantile, max_eq_right hx, sub_self, Pi.zero_apply]

/-- A clipped output probability differs from its baseline only on a compact set under decay at
infinity. -/
theorem hasCompactSupport_clippedOutput_probability {w : ℝ → ℝ}
    (hw : Tendsto w (cocompact ℝ) atBot) (σ η L H : ℝ) (hLH : -L ≤ H) :
    HasCompactSupport (fun x => gaussianCDF (clippedOutputQuantile w σ η L H x) - gaussianCDF (-L))
      := by
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
  filter_upwards [hw.eventually (eventually_le_atBot (-L - η / σ))] with x hx
  have hshift : w x + η / σ ≤ -L := by linarith only [hx]
  simp only [clippedOutputQuantile, max_eq_right hshift, min_eq_left hLH, sub_self, Pi.zero_apply]

/-- A finite family of bounded quantiles has common probability bounds strictly between zero and
one. -/
theorem exists_common_probability_bounds {k : ℕ} {u : Fin k → ℝ → ℝ} {a b : Fin k → ℝ}
    (hbound : ∀ i x, u i x ∈ Icc (a i) (b i)) :
    ∃ lo hi : ℝ, 0 < lo ∧ hi < 1 ∧ ∀ i x, gaussianCDF (u i x) ∈ Icc lo hi := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun i => max |a i| |b i|)
  refine ⟨gaussianCDF (-C), gaussianCDF C, gaussianCDF_pos _, gaussianCDF_lt_one _, ?_⟩
  intro i x
  have hi := (abs_le.mp ((abs_le_max_abs_abs (hbound i x).1 (hbound i x).2).trans (hC i)))
  exact ⟨strictMono_gaussianCDF.monotone hi.1, strictMono_gaussianCDF.monotone hi.2⟩

/-- The correlated three function comparison holds for shifted clipped quantiles with compatible
cutoffs. -/
theorem clipped_scalar_triple_comparison {u v w : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hutail : Tendsto u (cocompact ℝ) atBot) (hvtail : Tendsto v (cocompact ℝ) atBot)
    (hwtail : Tendsto w (cocompact ℝ) atBot)
    {p q ρ σ U V L H Lf Lg η : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1) (hσ : 0 < σ)
    (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ) (hη : 0 < η)
    (huU : ∀ x, u x ≤ U) (hvV : ∀ y, v y ≤ V)
    (horiginal : ∀ x y, p * u x + q * v y ≤ σ * w (p * x + q * y))
    (hLfU : -Lf ≤ U) (hLgV : -Lg ≤ V) (hLH : -L ≤ H)
    (hH : p * U + q * V + η ≤ σ * H)
    (hLf : q * V + σ * L + η ≤ p * Lf) (hLg : p * U + σ * L + η ≤ q * Lg) :
    quantileLinear (tripleTheta p q σ)
      (fun i => scaledGaussianMean
        (![fun x => gaussianCDF (clippedInputQuantile u Lf x),
           fun x => gaussianCDF (clippedInputQuantile v Lg x),
           fun x => gaussianCDF (clippedOutputQuantile w σ η L H x)] i) (tripleScales σ i)) ≤ 0 :=
             by
  let z : Fin 3 → ℝ → ℝ := ![clippedInputQuantile u Lf, clippedInputQuantile v Lg,
    clippedOutputQuantile w σ η L H]
  let f := fun i x => gaussianCDF (z i x)
  let c : Fin 3 → ℝ := ![gaussianCDF (-Lf), gaussianCDF (-Lg), gaussianCDF (-L)]
  have hf (i) : Continuous (f i) := by
    fin_cases i
    · exact continuous_gaussianCDF.comp (hu.max continuous_const)
    · exact continuous_gaussianCDF.comp (hv.max continuous_const)
    · exact continuous_gaussianCDF.comp ((hw.add continuous_const).max continuous_const |>.min
      continuous_const)
  have hcompact (i) : HasCompactSupport (fun x => f i x - c i) := by
    fin_cases i
    · exact hasCompactSupport_clippedInput_probability hutail Lf
    · exact hasCompactSupport_clippedInput_probability hvtail Lg
    · exact hasCompactSupport_clippedOutput_probability hwtail σ η L H hLH
  have hbounds (i) (x) : z i x ∈ Icc (![-Lf, -Lg, -L] i) (![U, V, H] i) := by
    fin_cases i
    · exact clippedInputQuantile_mem huU hLfU x
    · exact clippedInputQuantile_mem hvV hLgV x
    · exact clippedOutputQuantile_mem w σ η L H hLH x
  obtain ⟨lo, hi, hlo, hhi, hrange⟩ := exists_common_probability_bounds hbounds
  apply scalar_strict_triple_comparison hf c hcompact hlo hhi hrange hp hq hsum hρ hσ hvar hη
  intro x y
  change p * gaussianCDFChart.symm (gaussianCDF (clippedInputQuantile u Lf x)) +
    q * gaussianCDFChart.symm (gaussianCDF (clippedInputQuantile v Lg y)) -
    σ * gaussianCDFChart.symm (gaussianCDF (clippedOutputQuantile w σ η L H (p * x + q * y))) ≤ -η
  simp only [gaussianCDFChart_symm_gaussianCDF]
  exact compatible_quantile_clipping hp.le hq.le hσ (huU x) (hvV y) (horiginal x y)
    hLfU hLgV hH hLf hLg

end EhrhardGaussian.Ehrhard

end

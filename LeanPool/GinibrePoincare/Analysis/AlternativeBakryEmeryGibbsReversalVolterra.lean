/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsReversalVolterra.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalStopped
/-!
# Alternative Bakry Emery Gibbs reversal volterra

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbsOU_correctedBrownian_volterra`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem bakryEmeryGibbsConfigurationDrift_continuous {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) :
    Continuous (bakryEmeryGibbsConfigurationDrift W) := by
  apply continuous_pi
  intro j
  exact ((Complex.continuous_ofReal.comp ((hW.continuous_fderiv (by norm_num)).clm_apply
      continuous_const)).neg).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp ((hW.continuous_fderiv (by
        norm_num)).clm_apply continuous_const)))

/-- The actual Girsanov-corrected coordinate Brownian driver converts every
reference OU prefix into the concrete ordinary gradient equation. -/
theorem bakryEmeryGibbsOU_correctedBrownian_volterra {Ω : Type*} {n : ℕ}
    (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (Y : ℝ≥0 → Ω → Configuration n) (sample : Ω) (z : Configuration n) (θ : ℝ≥0)
    (hYC : Continuous (fun t => Y t sample))
    (hN0 : ginibreConfigurationBrownianNoise n B ((n : ℝ) ^ 2) sample 0 = 0)
    (hEq : ∀ t ≤ θ, Y t sample = z + ginibreConfigurationBrownianNoise n B ((n : ℝ) ^ 2) sample t +
      ∫ s in (0 : ℝ)..(t : ℝ), (-2 * (n : ℝ)) • Y s.toNNReal sample) :
    ∀ t ≤ θ, Y t sample = z + ginibreConfigurationBrownianNoise n
      (fun i r sample => B i r sample - B i 0 sample - ∫ s in (0 : ℝ)..(r : ℝ),
        bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) (bakryEmeryGibbsRelativePotential W)
          (Y s.toNNReal sample) i) ((n : ℝ)^2) sample t +
      ∫ s in (0 : ℝ)..(t : ℝ), bakryEmeryGibbsConfigurationDrift W (Y s.toNNReal sample) := by
  let y : ℝ → Configuration n := fun s => Y s.toNNReal sample
  have hy : Continuous y := hYC.comp continuous_real_toNNReal
  have hS : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  have hF : Continuous (fun s : ℝ => fun i =>
      bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) (bakryEmeryGibbsRelativePotential W) (y s) i) := by
    apply continuous_pi
    intro i
    exact (bakryEmeryGibbsPotentialTilt_continuous n ((n : ℝ)^2) _ hS i).comp hy
  intro t ht
  have hiD : IntervalIntegrable (fun s => bakryEmeryGibbsConfigurationDrift W (y s)) volume 0 (t :
      ℝ) := ((bakryEmeryGibbsConfigurationDrift_continuous W hW).comp hy).intervalIntegrable 0 (t :
          ℝ)
  have hiOU : IntervalIntegrable (fun s => (-2*(n : ℝ)) • y s) volume 0 (t : ℝ) := (hy.const_smul
      (-2*(n : ℝ))).intervalIntegrable 0 (t : ℝ)
  have hnoise := ginibreCorrectedBrownianNoise_eq n ((n : ℝ)^2) B
    (fun i r sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
      (bakryEmeryGibbsRelativePotential W) (Y r sample) i) sample (t : ℝ) t.property
      (hF.intervalIntegrable 0 t)
  rw [hN0, sub_zero] at hnoise
  have hI : (∫ s in (0 : ℝ)..(t : ℝ), ginibreBrownianEmbeddingCLM n ((n : ℝ)^2)
      (fun i => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
        (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal sample) i)) =
      (∫ s in (0 : ℝ)..(t : ℝ), bakryEmeryGibbsConfigurationDrift W (y s)) -
        ∫ s in (0 : ℝ)..(t : ℝ), (-2*(n : ℝ)) • y s := by
    rw [← intervalIntegral.integral_sub hiD hiOU]
    apply intervalIntegral.integral_congr
    intro s hs
    exact bakryEmeryGibbsConfigurationTilt_eq_drift hn W (hW.differentiable (by norm_num)) (y s)
  rw [hI] at hnoise
  rw [hnoise, hEq t ht]
  change _ = _
  dsimp only [y]
  abel

end
end GinibrePoincare

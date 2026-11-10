/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.CompactScalarApproximation
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Smooth approximating sequences for finite clipped scalar families -/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace EhrhardGaussian.Ehrhard

/-- Continuous functions constant off compact sets admit uniformly convergent smooth approximations
with compactly supported derivatives. -/
theorem exists_scalar_approximation_sequence {k : ℕ} {f : Fin k → ℝ → ℝ}
    (hf : ∀ i, Continuous (f i)) (c : Fin k → ℝ)
    (hcompact : ∀ i, HasCompactSupport (fun y => f i y - c i)) :
    ∃ g : ℕ → Fin k → ℝ → ℝ,
      (∀ n i, ContDiff ℝ ∞ (g n i)) ∧ (∀ n i, HasCompactSupport (deriv (g n i))) ∧
      (∀ n i y, |g n i y - f i y| < 1 / ((n : ℝ) + 1)) ∧
      ∀ i y, Tendsto (fun n => g n i y) atTop (𝓝 (f i y)) := by
  have hex (n : ℕ) (i : Fin k) := exists_smooth_compact_scalar_approximation (hf i) (hcompact i)
    (by positivity : 0 < 1 / ((n : ℝ) + 1))
  choose g hs hc hd he using hex
  refine ⟨g, hs, hd, he, ?_⟩
  intro i y
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Real.norm_eq_abs] using (he n i y).le

end EhrhardGaussian.Ehrhard

end

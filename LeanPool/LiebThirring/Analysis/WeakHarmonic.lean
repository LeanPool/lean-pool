/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.
public import LeanPool.LiebThirring.Analysis.WeakHarmonicDecay
import LeanPool.LiebThirring.Analysis.MaximumPrinciple
public import LeanPool.LiebThirring.Defs.Configuration
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
/-!
# Uniqueness for continuous decaying weakly harmonic functions

Continuity and decay at infinity imply a globally bounded range.

A continuous weakly harmonic function decaying at infinity vanishes.
-/
public section
open Filter MeasureTheory ContinuousLinearMap InnerProductSpace Laplacian
open scoped Topology Convolution ContDiff
namespace LiebThirring
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A continuous weakly harmonic function decaying at infinity vanishes. -/
theorem eq_zero_of_weak_laplacian_of_tendsto {w : E → ℝ}
    (hw : Continuous w)
    (hweak : ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, w x * Δ f x ∂μ) = 0)
    (hd : Tendsto w (cocompact E) (𝓝 0)) : w = 0 := by
  let b : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1),
      half_pos (by positivity), half_lt_self (by positivity)⟩
  have hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hz : ∀ n, (b n).normed μ ⋆[lsmul ℝ ℝ, μ] w = 0 := by
    intro n
    rw [convolution_real_comm]
    apply eq_zero_of_laplacian_eq_zero_of_tendsto
    · exact contDiff_convolution_of_continuous hw (b n).contDiff_normed (b
      n).hasCompactSupport_normed
    · exact laplacian_convolution_eq_zero_of_weak hw hweak
        (b n).contDiff_normed (b n).hasCompactSupport_normed
    · rw [convolution_real_comm]
      exact tendsto_normed_bump_convolution_cocompact hw hd (b n)
  funext x
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hb hw x
  simp only [hz, Pi.zero_apply] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- harmonic uniqueness on the three-dimensional carrier. -/
theorem weak_harmonic_eq_zero {w : Position → ℝ}
    (hw : Continuous w)
    (hweak : ∀ f : Position → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, w x * Δ f x) = 0)
    (hd : Tendsto w (cocompact Position) (𝓝 0)) : w = 0 :=
  eq_zero_of_weak_laplacian_of_tendsto hw hweak hd
end LiebThirring
end

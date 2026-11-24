/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DistributionRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.MollifierApproximation
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local smooth PSH approximation from positive distributional Levi form

Every compact subset of the domain has one open neighborhood on which a
sequence of globally smooth functions is plurisubharmonic and converges almost
everywhere to the given locally integrable density. A fixed compact cutoff
makes the density globally integrable, and shrinking normalized bump kernels
give the actual approximations. No monotonicity of this sequence is claimed.
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis

section Neighborhood

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- A compact set inside an open set has an open neighborhood whose fixed
radius closed balls all lie in one compact subset of the original open set.
The construction also applies to the empty compact set. -/
theorem exists_open_compact_closedBall_neighborhood {S V : Set E}
    (hS : IsCompact S) (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ R > 0, ∃ U K : Set E, IsOpen U ∧ S ⊆ U ∧ U ⊆ K ∧
      IsCompact K ∧ K ⊆ V ∧ ∀ z ∈ U, closedBall z R ⊆ K := by
  obtain ⟨ε, hε, hεV⟩ := hS.exists_thickening_subset_open hV hSV
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ + δ < ε := by dsimp [δ]; linarith
  refine ⟨δ, hδ, thickening δ S, cthickening (δ + δ) S, isOpen_thickening,
    self_subset_thickening hδ S, ?_, hS.cthickening,
    (cthickening_subset_thickening' hε hδε S).trans hεV, ?_⟩
  · exact thickening_subset_cthickening_of_le (by linarith) S
  · intro z hz
    exact (closedBall_subset_cthickening hz δ).trans
      (cthickening_thickening_subset hδ.le δ S)

end Neighborhood

section Approximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]
variable {Ω : Opens E} {u : E → ℝ} {K U : Set E}

/-- Compact localization leaves the actual mollification unchanged whenever
the kernel's support ball lies in the cutoff set. -/
theorem mollify_indicator_eq_of_closedBall_subset
    (φ : ContDiffBump (0 : E)) (z : E) (hzK : closedBall z φ.rOut ⊆ K) :
    mollify μ (K.indicator u) φ z = mollify μ u φ z :=
  translationPairing_indicator_eq u (φ.normed μ) z
    ((tsupport_mollifier_translate_subset μ φ z).trans hzK)

/-- The fixed compact cutoff converges to the original density almost
everywhere on each measurable inner set contained in the cutoff. -/
theorem ae_tendsto_mollify_indicator_on
    (hu : LocallyIntegrableOn u Ω μ) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hU : MeasurableSet U) (hUK : U ⊆ K) (R : ℝ) (hR : 0 < R) :
    ∀ᵐ x ∂μ.restrict U,
      Tendsto (fun n => mollify μ (K.indicator u) (shrinkingBump R hR n) x)
        atTop (𝓝 (u x)) := by
  have hg := (integrable_indicator_of_locallyIntegrableOn_isCompact hu hK hKΩ).locallyIntegrable
  filter_upwards [ae_restrict_of_ae (ae_tendsto_mollify μ hg R hR),
    ae_restrict_mem hU] with x hx hxU
  simpa only [indicator_of_mem (hUK hxU)] using hx

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- A density with nonnegative distributional Levi form admits actual smooth
PSH approximations on a common open neighborhood of every compact subset.
Every approximant is globally smooth; the density is only locally integrable
on Ω, and convergence is asserted only almost everywhere on the inner domain. -/
theorem exists_smooth_psh_ae_approximation
    (hu : LocallyIntegrableOn u Ω μ)
    (hT : HasNonnegativeDistributionalLevi (regularDistribution μ u hu))
    {S : Set E} (hS : IsCompact S) (hSΩ : S ⊆ Ω) :
    ∃ (U : Set E) (f : ℕ → E → ℝ), IsOpen U ∧ S ⊆ U ∧ U ⊆ Ω ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) ∧
      (∀ n, DiscPshOn (fun x => (f n x : EReal)) U) ∧
      (∀ n, PlurisubharmonicOn (fun x => (f n x : EReal)) U) ∧
      ∀ᵐ x ∂μ.restrict U, Tendsto (fun n => f n x) atTop (𝓝 (u x)) := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨R, hR, U, K, hU, hSU, hUK, hK, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood hS Ω.isOpen hSΩ
  let f : ℕ → E → ℝ := fun n => mollify μ (K.indicator u) (shrinkingBump R hR n)
  have hg := (integrable_indicator_of_locallyIntegrableOn_isCompact hu hK hKΩ).locallyIntegrable
  have hs (n : ℕ) (z : E) (hz : z ∈ U) :
      tsupport (fun x => (shrinkingBump R hR n).normed μ (x - z)) ⊆ K :=
    (tsupport_mollifier_translate_subset μ (shrinkingBump R hR n) z).trans
      ((closedBall_subset_closedBall (shrinkingBump_rOut_le R hR n)).trans (hball z hz))
  have hf (n : ℕ) : DiscPshOn (fun x => (f n x : EReal)) U :=
    discPshOn_translationPairing_indicator hu hT
      (shrinkingBump R hR n).hasCompactSupport_normed
      (shrinkingBump R hR n).contDiff_normed
      (shrinkingBump R hR n).nonneg_normed hK hKΩ (hs n)
  refine ⟨U, f, hU, hSU, hUK.trans hKΩ, ?_, hf, ?_, ?_⟩
  · exact fun n => contDiff_mollify μ hg (shrinkingBump R hR n)
  · exact fun n => (hf n).plurisubharmonicOn hU
  · exact ae_tendsto_mollify_indicator_on hu hK hKΩ hU.measurableSet hUK R hR

end Approximation

end SGPT.Foundations.Analysis

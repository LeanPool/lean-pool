/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroRapidityWave
public import LeanPool.VacuumBellSeparation.FreeField.WedgeFractionalWave
public import LeanPool.VacuumBellSeparation.FreeField.WedgeModularInclusion

/-!
# The literal unshifted wedge contour for original Cauchy data

The time-slice theorem produces an actual compact spacetime test function.
The entire-wave identity then identifies the maximal modular-power graph
vector with Psi on the complex boosted mass shell. The resulting integral
is the genuine physical Hilbert norm.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

theorem norm_L2_sq_eq_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (v : Lp ℂ 2 μ) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner v v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => inner_self_eq_norm_sq (𝕜 := ℂ) (v x)

theorem timeZero_mem_wedgePower_graph_contour {m : ℝ} (hm : 0 < m)
    (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ leftWedgeTimeZero 0)
    (hg : tsupport u.2.1 ⊆ leftWedgeTimeZero 0)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (timeZeroL2 hm u, χ) ∈ (physicalRapidityExponential hm c).graph ∧
      χ =ᵐ[oneParticleMeasure m] (fun p => complexSourceWave u
        (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)) := by
  obtain ⟨F, hF, heq⟩ :=
    exists_spacetimeSourceL2_of_timeZeroSource_leftWedge hm 0 u hf hg
  let ζ : ℂ := ((2 * Real.pi * c : ℝ) : ℂ) * Complex.I
  have hζ := wedgeWave_angle_mem_strip hc hc2
  refine ⟨wedgeWaveL2 hm F hF ζ hζ, ?_, ?_⟩
  · simpa only [heq] using wedgeWave_mem_physicalRapidityPower_graph hm F hF hc hc2
  · filter_upwards [wedgeWaveL2_ae hm F hF ζ hζ] with p hp
    exact hp.trans (wedgeWave_eq_complexSourceWave_of_L2_eq hm F u heq ζ p)

/-- The actual square-integrable contour and exact graph norm. -/
theorem timeZero_wedgePower_contour_norm {m : ℝ} (hm : 0 < m)
    (u : TimeZeroSource)
    (hf : tsupport u.1.1 ⊆ leftWedgeTimeZero 0)
    (hg : tsupport u.2.1 ⊆ leftWedgeTimeZero 0)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (timeZeroL2 hm u, χ) ∈ (physicalRapidityExponential hm c).graph ∧
      MemLp (fun p => complexSourceWave u
        (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p))
        2 (oneParticleMeasure m) ∧
      ‖χ‖ ^ 2 = ∫ p, ‖complexSourceWave u
        (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)‖ ^ 2
        ∂oneParticleMeasure m := by
  obtain ⟨χ, hχ, hae⟩ := timeZero_mem_wedgePower_graph_contour hm u hf hg hc hc2
  refine ⟨χ, hχ, ?_, ?_⟩
  · exact MemLp.ae_eq hae (Lp.memLp χ)
  · rw [norm_L2_sq_eq_integral_norm_sq]
    exact integral_congr_ae (hae.mono fun _ hp =>
      congrArg (fun z : ℂ => ‖z‖ ^ 2) hp)

/-- The containing-wedge norm bound for original localized real test pairs. -/
theorem complexSourceWave_contour_le_sourceWeight {m : ℝ} (hm : 0 < m)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ⊆ leftWedgeTimeZero 0)
    (u : SourceTestSpace hm U) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∫ p, ‖complexSourceWave u.1
      (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p)‖ ^ 2
      ∂oneParticleMeasure m) ≤
      ‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U))‖ ^ 2 := by
  obtain ⟨χ, hχ, _, hnorm⟩ := timeZero_wedgePower_contour_norm hm u.1
    (u.2.1.trans hU) (u.2.2.trans hU) hc.le hc2
  obtain ⟨ψ, hψ, hbound⟩ := physicalRapidityExponential_containing_leftWedge hm hU hc hc2
    (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U))
  rw [complexSourceMap_ofReal_test] at hψ
  have he := (physicalRapidityExponential hm c).mem_graph_snd_inj hχ hψ rfl
  rw [← hnorm, he]
  exact pow_le_pow_left₀ (norm_nonneg _) hbound 2

end VacuumBellSeparation

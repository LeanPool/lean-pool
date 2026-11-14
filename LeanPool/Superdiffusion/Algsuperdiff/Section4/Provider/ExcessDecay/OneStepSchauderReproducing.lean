/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderFlux
public import Mathlib.Analysis.Convolution

/-!
# OneStepSchauderReproducing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The reproducing convolution

A harmonic function reproduces itself against any **unit-mass radial** kernel:
integrating the mean value property in the radius against the radial profile
gives `u(x₀) = (K_ε ⋆ u)(x₀)` whenever `K_ε` is supported in a ball on which
`u` is harmonic.  This module proves that identity and packages it as a
convolution, which is the exact form the interior estimates differentiate.
-/

-- ==== the reproducing formula ====
open scoped Real
open MeasureTheory Metric Set InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Reproducing identity for a radial kernel.**  Let `u ∈ C²` be harmonic on `Metric.ball x R` and
let `K` be a continuous, radial, compactly supported kernel of unit mass whose
support sits inside the
ball of radius `ρ ≤ R` (i.e. `K z = 0` whenever `ρ ≤ ‖z‖`).  Then `K` reproduces `u` at the center:
  `∫ y, K (y - x) · u y = u x`. -/
theorem reproducing_of_radial [NeZero d] {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u)
    {x : 𝔼} {R : ℝ} (hharm : HarmonicOnNhd u (ball x R))
    {K : 𝔼 → ℝ} (hKc : Continuous K) (hKcs : HasCompactSupport K)
    (hKrad : ∀ {a b : 𝔼}, ‖a‖ = ‖b‖ → K a = K b)
    {ρ : ℝ} (hρR : ρ ≤ R) (hKsupp : ∀ z : 𝔼, ρ ≤ ‖z‖ → K z = 0)
    (hKmass : ∫ z, K z = 1) :
    ∫ y, K (y - x) * u y = u x := by
  classical
  -- a fixed unit vector `e`, for evaluating the radial profile of `K`
  set i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ with hi0
  set e : 𝔼 := EuclideanSpace.single i0 (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single]; norm_num
  -- integrability facts
  have hucomp : Continuous (fun z : 𝔼 => u (x + z)) :=
    hu.continuous.comp (continuous_const.add continuous_id)
  have hKint : Integrable K := hKc.integrable_of_hasCompactSupport hKcs
  have hGcont : Continuous (fun z : 𝔼 => K z * u (x + z)) := hKc.mul hucomp
  have hGsupp : HasCompactSupport (fun z : 𝔼 => K z * u (x + z)) := hKcs.mul_right
  have hGint : Integrable (fun z : 𝔼 => K z * u (x + z)) :=
    hGcont.integrable_of_hasCompactSupport hGsupp
  -- translate the integrand to the origin
  have htrans : ∫ y, K (y - x) * u y = ∫ z, K z * u (x + z) := by
    have h := integral_add_left_eq_self (μ := (volume : Measure 𝔼))
      (fun y : 𝔼 => K (y - x) * u y) x
    simp only [add_sub_cancel_left] at h
    exact h.symm
  -- polar bridge for `K·u` and for `K`
  have hpolarG : (∫ z, K z * u (x + z))
      = ∫ s in Ioi (0 : ℝ),
          s ^ (d - 1) • ∫ ω, K (s • (ω : 𝔼)) * u (x + s • (ω : 𝔼)) ∂(sphereMeasure d) :=
    integral_eq_integral_Ioi_sphere hGint
  have hpolarK : (∫ z, K z)
      = ∫ s in Ioi (0 : ℝ), s ^ (d - 1) • ∫ ω, K (s • (ω : 𝔼)) ∂(sphereMeasure d) :=
    integral_eq_integral_Ioi_sphere hKint
  -- mass in radial form
  have hKinner : ∀ s ∈ Ioi (0 : ℝ), (∫ ω, K (s • (ω : 𝔼)) ∂(sphereMeasure d))
      = (sphereMeasure d).real univ * K (s • e) := by
    intro s _
    have hfe : (fun ω : sphere (0 : 𝔼) 1 => K (s • (ω : 𝔼))) = fun _ => K (s • e) := by
      funext ω
      exact hKrad (by rw [norm_smul, norm_smul, he, mem_sphere_zero_iff_norm.mp ω.2])
    rw [hfe, integral_const, smul_eq_mul]
  have hKmass' :
      (∫ s in Ioi (0 : ℝ), s ^ (d - 1) • ((sphereMeasure d).real univ * K (s • e))) = 1 := by
    have hcongr : (∫ s in Ioi (0 : ℝ), s ^ (d - 1) • ((sphereMeasure d).real univ * K (s • e)))
        = ∫ s in Ioi (0 : ℝ), s ^ (d - 1) • ∫ ω, K (s • (ω : 𝔼)) ∂(sphereMeasure d) :=
      setIntegral_congr_fun measurableSet_Ioi (fun s hs => by rw [hKinner s hs])
    rw [hcongr, ← hpolarK, hKmass]
  -- the `K·u` radial integrand collapses to `u x · (…)` via radiality + the sphere MVP
  have hGinner : ∀ s ∈ Ioi (0 : ℝ),
      s ^ (d - 1) • (∫ ω, K (s • (ω : 𝔼)) * u (x + s • (ω : 𝔼)) ∂(sphereMeasure d))
        = u x * (s ^ (d - 1) • ((sphereMeasure d).real univ * K (s • e))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hcong : (∫ ω, K (s • (ω : 𝔼)) * u (x + s • (ω : 𝔼)) ∂(sphereMeasure d))
        = K (s • e) * ((sphereMeasure d).real univ • sphereAverage x s u) := by
      have hfe : (fun ω : sphere (0 : 𝔼) 1 => K (s • (ω : 𝔼)) * u (x + s • (ω : 𝔼)))
          = fun ω : sphere (0 : 𝔼) 1 => K (s • e) * u (x + s • (ω : 𝔼)) := by
        funext ω
        rw [hKrad (show ‖s • (ω : 𝔼)‖ = ‖s • e‖ from by
          rw [norm_smul, norm_smul, he, mem_sphere_zero_iff_norm.mp ω.2])]
      rw [hfe, integral_const_mul, integral_sphere_eq_measureReal_smul_sphereAverage]
    rw [hcong]
    by_cases hc0 : K (s • e) = 0
    · simp only [hc0, zero_mul, smul_zero, mul_zero]
    · have hsρ : s < ρ := by
        by_contra hcon
        exact hc0 (hKsupp (s • e)
          (by rw [norm_smul, he, Real.norm_eq_abs, abs_of_pos hs0, mul_one]
              exact le_of_not_gt hcon))
      have hsR : s < R := lt_of_lt_of_le hsρ hρR
      rw [sphereAverage_eq_center_of_harmonic hu hharm s ⟨le_of_lt hs0, hsR⟩]
      simp only [smul_eq_mul]; ring
  -- assemble
  rw [htrans, hpolarG, setIntegral_congr_fun measurableSet_Ioi hGinner,
    integral_const_mul, hKmass', mul_one]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== the convolution representation ====
open scoped Real Convolution Topology
open MeasureTheory Metric Set InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Pointwise value of the mollified reproducing convolution.**  Let `u ∈ C²` be harmonic on
`Metric.ball x' R'` with `ε ≤ R'`, and suppose the `ε`-ball around `x'` sits inside the localization
ball `ball x₀ r₀`.  Then the convolution of the `ε`-scaled kernel with the localized field evaluates
to `u x'` at `x'`. -/
theorem convolution_radialKernelScaled_indicator_apply [NeZero d] {u : 𝔼 → ℝ}
    (hu : ContDiff ℝ 2 u) {x₀ x' : 𝔼} {r₀ ε R' : ℝ} (hε : 0 < ε) (hεR' : ε ≤ R')
    (hball : ball x' ε ⊆ ball x₀ r₀) (hharm : HarmonicOnNhd u (ball x' R')) :
    (radialKernelScaled d ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Set.indicator (ball x₀ r₀) u) x' = u x' := by
  rw [convolution_lsmul_swap]
  have step1 : (fun t : 𝔼 => radialKernelScaled d ε (x' - t) • Set.indicator (ball x₀ r₀) u t)
      = (fun t : 𝔼 => radialKernelScaled d ε (t - x') * u t) := by
    funext t
    by_cases ht : t ∈ ball x' ε
    · have htr : t ∈ ball x₀ r₀ := hball ht
      rw [Set.indicator_of_mem htr, smul_eq_mul,
        radialKernelScaled_radial d (show ‖x' - t‖ = ‖t - x'‖ from norm_sub_rev x' t)]
    · have hdist : ε ≤ dist t x' := by
        have h := ht; rw [Metric.mem_ball] at h; exact le_of_not_gt h
      have hz1 : radialKernelScaled d ε (x' - t) = 0 :=
        radialKernelScaled_eq_zero_of_le_norm d hε
          (by rw [norm_sub_rev, ← dist_eq_norm]; exact hdist)
      have hz2 : radialKernelScaled d ε (t - x') = 0 :=
        radialKernelScaled_eq_zero_of_le_norm d hε (by rw [← dist_eq_norm]; exact hdist)
      rw [hz1, hz2, zero_smul, zero_mul]
  rw [step1]
  exact reproducing_of_radial hu hharm (radialKernelScaled_continuous d)
    (radialKernelScaled_hasCompactSupport d hε)
    (fun h => radialKernelScaled_radial d h) hεR'
    (fun z hz => radialKernelScaled_eq_zero_of_le_norm d hε hz)
    (radialKernelScaled_integral_eq_one d hε)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder


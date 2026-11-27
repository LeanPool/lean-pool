/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveStripBound
public import LeanPool.VacuumBellSeparation.FreeField.BoundedStripUniqueness
public import LeanPool.VacuumBellSeparation.FreeField.RapidityFrequencyCutoff
public import LeanPool.VacuumBellSeparation.FreeField.PhysicalRapidityExponential

/-!
# Full multiplier domain for original compact wedge waves

Bounded frequency cutoffs allow the genuine Hilbert-valued three-lines theorem.
Taking their countable union identifies the actual Fourier representatives,
including the upper boundary. The resulting graph statement uses the maximal
physical exponential; its domain is not supplied as a hypothesis.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped InnerProductSpace

theorem wedgeWaveExtendedL2_ofReal {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (t : ℝ) :
    wedgeWaveExtendedL2 hm F hF t = oneParticleBoost hm (-t) (oneParticleL2 hm F) := by
  have ht : (t : ℂ) ∈ closedRapidityStrip := ⟨by simp, by simpa using Real.pi_pos.le⟩
  rw [wedgeWaveExtendedL2, dite_eq_left ht, wedgeWaveL2_eq_boost_imaginary hm F hF t ht]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero, zero_mul,
    wedgeWaveL2_zero]
  rfl

theorem rapidityCutoff_wedgeWave {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (N : ℕ) {z : ℂ} (hz : z ∈ closedRapidityStrip) :
    rapidityCutoff N (oneParticleRapidityFourier hm (wedgeWaveExtendedL2 hm F hF z)) =
      rapidityCutoffEvolution N (oneParticleRapidityFourier hm (oneParticleL2 hm F)) z := by
  let T := (rapidityCutoff N).comp (oneParticleRapidityFourier
    hm).toContinuousLinearEquiv.toContinuousLinearMap
  let ψ := oneParticleRapidityFourier hm (oneParticleL2 hm F)
  let g : ℂ → RapidityL2 := fun w =>
    T (wedgeWaveExtendedL2 hm F hF w) - rapidityCutoffEvolution N ψ w
  have hd : DiffContOnCl ℂ g openRapidityStrip :=
    (T.differentiable.comp_diffContOnCl (diffContOnCl_wedgeWaveExtendedL2 hm F hF)).sub
      (differentiable_rapidityCutoffEvolution N ψ).diffContOnCl
  obtain ⟨M, hM⟩ := exists_uniform_norm_wedgeWaveExtendedL2 hm F hF
  have hb (w : ℂ) (hw₀ : 0 ≤ w.im) (hwπ : w.im ≤ Real.pi) :
      ‖g w‖ ≤ M + Real.exp (2 * Real.pi ^ 2 * N) * ‖ψ‖ := by
    have h₁ : ‖T (wedgeWaveExtendedL2 hm F hF w)‖ ≤ M := by
      change ‖rapidityCutoff N
        (oneParticleRapidityFourier hm (wedgeWaveExtendedL2 hm F hF w))‖ ≤ M
      exact (norm_rapidityCutoff_apply_le N _).trans
        ((oneParticleRapidityFourier hm).norm_map _ |>.le.trans (hM w ⟨hw₀, hwπ⟩))
    exact (norm_sub_le _ _).trans (add_le_add h₁
      (norm_rapidityCutoffEvolution_le N ψ hw₀ hwπ))
  have hzero (t : ℝ) : g t = 0 := by
    dsimp [g, T, ψ]
    rw [wedgeWaveExtendedL2_ofReal,
      oneParticleRapidityFourier_boost, rapidityCutoffEvolution_ofReal, sub_self]
  exact sub_eq_zero.mp
    (eq_zero_on_horizontalClosedStrip_of_bounded_lower_zero Real.pi_pos g hd hb hzero hz.1 hz.2)

theorem oneParticleRapidityFourier_wedgeWave_ae {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) {z : ℂ} (hz : z ∈ closedRapidityStrip) :
    oneParticleRapidityFourier hm (wedgeWaveExtendedL2 hm F hF z) =ᵐ[rapidityMeasure]
      fun ξ => Complex.exp (z * ((2 * Real.pi * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I)) *
        oneParticleRapidityFourier hm (oneParticleL2 hm F) ξ := by
  have hN (N : ℕ) : ∀ᵐ ξ ∂rapidityMeasure,
      rapidityFrequencyCutoff N ξ *
        oneParticleRapidityFourier hm (wedgeWaveExtendedL2 hm F hF z) ξ =
      rapidityFrequencyCutoff N ξ *
        (Complex.exp (z * ((2 * Real.pi * ⟪e₁, ξ⟫_ℝ : ℝ) * Complex.I)) *
          oneParticleRapidityFourier hm (oneParticleL2 hm F) ξ) := by
    have he := rapidityCutoff_wedgeWave hm F hF N hz
    filter_upwards [rapidityCutoff_ae N
      (oneParticleRapidityFourier hm (wedgeWaveExtendedL2 hm F hF z)),
      rapidityCutoffEvolution_ae N (oneParticleRapidityFourier hm (oneParticleL2 hm F)) z]
      with ξ hc hevol
    rw [he] at hc
    exact hc.symm.trans hevol
  filter_upwards [ae_all_iff.mpr hN] with ξ hξ
  obtain ⟨N, hN⟩ := exists_nat_ge |⟪e₁, ξ⟫_ℝ|
  simpa only [rapidityFrequencyCutoff, ite_eq_left hN, one_mul] using hξ N

/-- Actual domain membership and exact upper boundary for every original compact
left-wedge test source, in the maximal physical half-power graph. -/
theorem wedgeWave_upper_mem_physicalRapidityHalf_graph {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge 0) :
    (oneParticleL2 hm F,
      wedgeWaveL2 hm F hF ((Real.pi : ℂ) * Complex.I) (by simp [Real.pi_pos.le])) ∈
      (physicalRapidityExponential hm (1 / 2)).graph := by
  rw [physicalRapidityExponential_mem_graph]
  have hz : ((Real.pi : ℂ) * Complex.I) ∈ closedRapidityStrip := by
    simp [closedRapidityStrip, Real.pi_pos.le]
  have h := oneParticleRapidityFourier_wedgeWave_ae hm F hF hz
  simp only [wedgeWaveExtendedL2, dite_eq_left hz] at h
  filter_upwards [h] with ξ hξ
  rw [hξ]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  unfold rapidityFrequencyExponent
  push_cast
  rw [mul_mul_mul_comm, Complex.I_mul_I]
  ring

end VacuumBellSeparation

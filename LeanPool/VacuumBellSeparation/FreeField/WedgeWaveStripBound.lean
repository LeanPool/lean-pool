/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveHolomorphic

/-!
# Uniform Hilbert bound on the complete closed rapidity strip

Real shifts act by the actual isometric physical boost. The imaginary segment
is compact and the physical wave is strongly continuous there. Thus its Hilbert
norm is bounded uniformly even as the real part tends to either infinity.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology

theorem wedgeWaveL2_eq_boost_imaginary {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (ζ : ℂ) (hζ : ζ ∈ closedRapidityStrip) :
    wedgeWaveL2 hm F hF ζ hζ = oneParticleBoostIsometry hm (-ζ.re)
      (wedgeWaveL2 hm F hF ((ζ.im : ℂ) * Complex.I) (by simpa [closedRapidityStrip] using hζ)) := by
  apply Lp.ext
  have hre := (measurePreserving_shellBoost hm ζ.re).quasiMeasurePreserving.ae_eq_comp
    (wedgeWaveL2_ae hm F hF ((ζ.im : ℂ) * Complex.I) (by simpa [closedRapidityStrip] using hζ))
  filter_upwards [wedgeWaveL2_ae hm F hF ζ hζ,
    oneParticleBoostIsometry_ae hm (-ζ.re)
      (wedgeWaveL2 hm F hF ((ζ.im : ℂ) * Complex.I) (by simpa [closedRapidityStrip] using hζ)), hre]
    with p hp hboost himag
  dsimp only [Function.comp_apply] at himag
  rw [hp, hboost]
  simp only [neg_neg, Function.comp_apply]
  exact (wedgeWave_eq_imaginary_boost m F ζ p).trans himag.symm

theorem continuousOn_wedgeWaveExtendedL2 {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) :
    ContinuousOn (wedgeWaveExtendedL2 hm F hF) closedRapidityStrip := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert continuous_wedgeWaveClosedStripL2 hm F hF using 1
  funext ζ
  simp only [Set.domRestrict_apply, wedgeWaveExtendedL2, dite_eq_left ζ.2,
    wedgeWaveClosedStripL2]

theorem exists_uniform_norm_wedgeWaveExtendedL2 {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge 0) :
    ∃ M : ℝ, ∀ ζ ∈ closedRapidityStrip, ‖wedgeWaveExtendedL2 hm F hF ζ‖ ≤ M := by
  let γ : ℝ → ℂ := fun θ => (θ : ℂ) * Complex.I
  have hcγ : Continuous γ := Complex.continuous_ofReal.mul continuous_const
  have hγ : Set.MapsTo γ (Set.Icc 0 Real.pi) closedRapidityStrip := by
    intro θ hθ
    simpa [γ, closedRapidityStrip] using hθ
  have hc : ContinuousOn (fun θ => wedgeWaveExtendedL2 hm F hF (γ θ)) (Set.Icc 0 Real.pi) :=
    (continuousOn_wedgeWaveExtendedL2 hm F hF).comp hcγ.continuousOn hγ
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun ζ hζ => ?_⟩
  have hi : γ ζ.im ∈ closedRapidityStrip := hγ hζ
  have h := hM ζ.im hζ
  simp only [wedgeWaveExtendedL2, dite_eq_left hi] at h
  simp only [wedgeWaveExtendedL2, dite_eq_left hζ]
  rw [wedgeWaveL2_eq_boost_imaginary hm F hF ζ hζ,
    (oneParticleBoostIsometry hm (-ζ.re)).norm_map]
  exact h

theorem diffContOnCl_wedgeWaveExtendedL2 {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge 0) :
    DiffContOnCl ℂ (wedgeWaveExtendedL2 hm F hF) openRapidityStrip := by
  refine ⟨differentiableOn_wedgeWaveExtendedL2 hm F hF, ?_⟩
  have he : closure openRapidityStrip = closedRapidityStrip := by
    change closure (Complex.im ⁻¹' Set.Ioo 0 Real.pi) = Complex.im ⁻¹' Set.Icc 0 Real.pi
    rw [Complex.closure_preimage_im, closure_Ioo Real.pi_pos.ne]
  rw [he]
  exact continuousOn_wedgeWaveExtendedL2 hm F hF

end VacuumBellSeparation

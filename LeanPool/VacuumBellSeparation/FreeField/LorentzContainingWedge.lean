/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceRangeIsometry
public import LeanPool.VacuumBellSeparation.FreeField.LorentzWedgeContour
public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceBall

/-!
# Containing Lorentz wedges for the original completed ball sources

The range inclusion is proved from the actual ball time-slice theorem and
closedness of the completed wedge source range. Consequently the full
unitarily transported maximal power acts on every original completed
complex source, with the original source-weight bound. For compact real
test pairs this bounds the literal damped complex-shell integral.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

variable {m : ℝ} (hm : 0 < m) (ℓ : ℝ)
  (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
  (hfuture : IsOrthochronousMap Λ)

theorem oneParticleLorentz_symm_oneParticleL2 (F : RealTestFunction) :
    (oneParticleLorentz hm Λ hΛ hfuture).symm (oneParticleL2 hm F) =
      oneParticleL2 hm (F.compCLE Λ) := by
  apply (oneParticleLorentz hm Λ hΛ hfuture).injective
  rw [LinearIsometryEquiv.apply_symm_apply, oneParticleLorentz_oneParticleL2,
    RealTestFunction.compCLE_compCLE_symm]

variable {U : Set (EuclideanSpace ℝ (Fin 3))} {R : ℝ}
  (hR : 0 < R) (hU : U ⊆ Metric.ball 0 R)
  (hregion : doubleCone (0, (0 : EuclideanSpace ℝ (Fin 3))) R ⊆ Λ '' leftWedge ℓ)

include hR hU hregion in
theorem sourceEmbedding_mem_lorentzWedge (z : SourceHilbert hm U) :
    (oneParticleLorentz hm Λ hΛ hfuture).symm (sourceEmbedding hm U z) ∈
      sourceRealSpace hm (leftWedgeTimeZero ℓ) := by
  refine UniformSpace.Completion.induction_on z
    ((sourceRealSpace hm (leftWedgeTimeZero ℓ)).isClosed.preimage
      ((oneParticleLorentz hm Λ hΛ hfuture).symm.continuous.comp
        (sourceEmbedding hm U).continuous)) ?_
  intro u
  rw [sourceEmbedding_coe]
  obtain ⟨F, hF, heq⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR 0 u.1
    (u.2.1.trans hU) (u.2.2.trans hU)
  rw [← heq, oneParticleLorentz_symm_oneParticleL2]
  exact oneParticleL2_mem_sourceRealSpace_leftWedge hm ℓ (F.compCLE Λ)
    (tsupport_compLorentz_subset_wedge Λ ℓ F (hF.trans hregion))

include hR hU hregion in
/-- Full-domain containing-wedge estimate on every original completed source. -/
theorem lorentzWedgeExponential_containing_ball
    {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (z : ComplexSourceHilbert hm U) :
    ∃ χ : Lp ℂ 2 (oneParticleMeasure m),
      (complexSourceMap hm U z, χ) ∈
        (unitaryPartialTransport (oneParticleLorentz hm Λ hΛ hfuture)
          (shiftedWedgeExponential hm ℓ c)).graph ∧
        ‖χ‖ ≤ ‖sourceModularWeight hm U c z‖ := by
  let T := oneParticleLorentz hm Λ hΛ hfuture
  have hT : ∀ x : SourceHilbert hm U, T.symm (sourceEmbedding hm U x) ∈
      sourceRealSpace hm (leftWedgeTimeZero ℓ) :=
    sourceEmbedding_mem_lorentzWedge hm ℓ Λ hΛ hfuture hR hU hregion
  let J := complexSourceRangeIsometry hm T.symm hT
  let ψ := leftWedgeSourcePolarUnitary hm ℓ
    (sourceModularWeight hm (leftWedgeTimeZero ℓ) c (J z))
  refine ⟨T ψ, ?_, ?_⟩
  · rw [unitaryPartialTransport_mem_graph, LinearIsometryEquiv.symm_apply_apply]
    have hg := shiftedWedgeExponential_source_graph hm ℓ hc.le hc2 (J z)
    have he := complexSourceMap_rangeIsometry hm T.symm hT z
    change complexSourceMap hm (leftWedgeTimeZero ℓ) (J z) = T.symm (complexSourceMap hm U z) at he
    simpa only [he] using hg
  · change ‖T (leftWedgeSourcePolarUnitary hm ℓ
      (sourceModularWeight hm (leftWedgeTimeZero ℓ) c (J z)))‖ ≤ _
    rw [T.norm_map, LinearIsometryEquiv.norm_map]
    exact sourceModularWeight_rangeIsometry_norm hm T.symm hT hc hc2 z

include hΛ hfuture hR hU hregion in
/-- The exact Lorentz contour estimate, with no spacetime representative premise. -/
theorem complexSourceWave_lorentzContour_le_sourceWeight
    (u : SourceTestSpace hm U) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∫ p, Real.exp (-2 * ℓ * dispersion m p * Real.sin (2 * Real.pi * c)) *
      ‖complexSourceWave u.1 (complexifiedSpacetimeMap Λ
        (complexShellBoost m (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I) p))‖ ^ 2
      ∂oneParticleMeasure m) ≤
      ‖sourceModularWeight hm U c
        (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U))‖ ^ 2 := by
  obtain ⟨F, hF, heq⟩ := exists_spacetimeSourceL2_of_timeZeroSource_ball hm hR 0 u.1
    (u.2.1.trans hU) (u.2.2.trans hU)
  obtain ⟨χ, hχ, hnorm⟩ := timeZero_lorentzWedge_contour_norm hm ℓ Λ hΛ hfuture
    F u.1 heq (hF.trans hregion) hc.le hc2
  obtain ⟨ψ, hψ, hbound⟩ := lorentzWedgeExponential_containing_ball hm ℓ Λ hΛ hfuture
    hR hU hregion hc hc2 (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U))
  rw [complexSourceMap_ofReal_test] at hψ
  have he := (unitaryPartialTransport (oneParticleLorentz hm Λ hΛ hfuture)
    (shiftedWedgeExponential hm ℓ c)).mem_graph_snd_inj hχ hψ rfl
  rw [← hnorm, he]
  nlinarith [norm_nonneg ψ, norm_nonneg (sourceModularWeight hm U c
    (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U)))]

end VacuumBellSeparation

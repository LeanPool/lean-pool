/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ControlledContourRectangle
public import LeanPool.VacuumBellSeparation.Shell.RectangleJacobianBound

/-!
# Fixed-mass nine-dimensional contour Jacobian

Mass is a retained parameter rather than an integration variable. The
slice derivative is derived from the actual full contour derivative.
One fixed linear identification is used throughout a neighbourhood;
its determinant bound is uniform in the nearby mass coordinate.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped Topology

/-- Shell physical parameters with underlying type `(Fin 6 → ℝ) × (Fin 3 → ℝ) abbrev
ShellPhysicalCoordinates := (Fin 3 → ℂ) × (Fin 3 → ℝ)`. -/
abbrev ShellPhysicalParameters := (Fin 6 → ℝ) × (Fin 3 → ℝ)
/-- Shell physical coordinates with underlying type `(Fin 3 → ℂ) × (Fin 3 → ℝ)`. -/
abbrev ShellPhysicalCoordinates := (Fin 3 → ℂ) × (Fin 3 → ℝ)

/-- The map from real contour parameters into the complex shell at fixed mass. -/
noncomputable def fixedMassContourEmbedding (τ : ℝ) (q : ShellPhysicalParameters) :
    ShellContourParameters := (q.1, (τ, q.2))

/-- Continuous linear map for the fixed mass contour inclusion, of type `ShellPhysicalParameters
→L[ℝ] ShellContourParameters`. -/
noncomputable def fixedMassContourInclusion : ShellPhysicalParameters →L[ℝ]
  ShellContourParameters :=
  (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) (Fin 3 → ℝ)).prod
    ((0 : ShellPhysicalParameters →L[ℝ] ℝ).prod
      (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (Fin 3 → ℝ)))

theorem hasFDerivAt_fixedMassContourEmbedding (τ : ℝ) (q : ShellPhysicalParameters) :
    HasFDerivAt (fixedMassContourEmbedding τ) fixedMassContourInclusion q := by
  exact (ContinuousLinearMap.fst ℝ (Fin 6 → ℝ) (Fin 3 → ℝ)).hasFDerivAt.prodMk
    ((hasFDerivAt_const τ q).prodMk
      (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (Fin 3 → ℝ)).hasFDerivAt)

/-- Fixed mass contour map. -/
noncomputable def fixedMassContourMap (m B θ τ : ℝ) (q : ShellPhysicalParameters) :
    ShellPhysicalCoordinates :=
  (fullContourMap m B θ (fixedMassContourEmbedding τ q), q.2)

/-- Continuous linear map for the fixed mass contour derivative, of type `ShellPhysicalParameters
→L[ℝ] ShellPhysicalCoordinates`. -/
noncomputable def fixedMassContourDerivative (m B θ : ℝ) (q : ShellContourParameters) :
    ShellPhysicalParameters →L[ℝ] ShellPhysicalCoordinates :=
  ((fderiv ℝ (fullContourMap m B θ) q).comp fixedMassContourInclusion).prod
    (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (Fin 3 → ℝ))

theorem hasFDerivAt_fixedMassContourMap (m B θ τ : ℝ) (q : ShellPhysicalParameters)
    (hq : DifferentiableAt ℝ (fullContourMap m B θ) (fixedMassContourEmbedding τ q)) :
    HasFDerivAt (fixedMassContourMap m B θ τ)
      (fixedMassContourDerivative m B θ (fixedMassContourEmbedding τ q)) q :=
  (hq.hasFDerivAt.comp q (hasFDerivAt_fixedMassContourEmbedding τ q)).prodMk
    (ContinuousLinearMap.snd ℝ (Fin 6 → ℝ) (Fin 3 → ℝ)).hasFDerivAt

/-- Continuous linear equivalence for the fixed mass contour linear coordinates, of type
`ShellPhysicalParameters ≃L[ℝ] ShellPhysicalCoordinates`. -/
noncomputable def fixedMassContourLinearCoordinates (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    ShellPhysicalParameters ≃L[ℝ] ShellPhysicalCoordinates :=
  (referenceContourDerivativeEquiv m hB hθ).prodCongr (ContinuousLinearEquiv.refl ℝ _)

theorem continuousAt_fixedMassContourDerivative (m θ : ℝ) {B : ℝ} (hB : 0 < B) :
    ContinuousAt (fixedMassContourDerivative m B θ) 0 := by
  have hc := (contDiffAt_fullContourMap hB m θ).continuousAt_fderiv (by simp)
  apply continuousAt_clm_apply.mpr
  intro v
  exact (hc.clm_apply continuousAt_const).prodMk continuousAt_const

theorem fixedMassContour_uniform_jacobian_bound (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ q : ShellContourParameters, ‖q‖ < r →
      DifferentiableAt ℝ (fullContourMap m B θ) q ∧
      |((fixedMassContourLinearCoordinates m hB hθ).symm.toContinuousLinearMap.comp
        (fixedMassContourDerivative m B θ q)).det| ≤ C := by
  let J := fixedMassContourLinearCoordinates m hB hθ
  let d : ShellContourParameters → ℝ := fun q =>
    |(J.symm.toContinuousLinearMap.comp (fixedMassContourDerivative m B θ q)).det|
  have hd : ContinuousAt d 0 :=
    (ContinuousLinearMap.continuous_det.continuousAt.comp
      (continuousAt_const.clm_comp (continuousAt_fixedMassContourDerivative m θ hB))).abs
  have hc1 : ContDiffAt ℝ 1 (fullContourMap m B θ) 0 :=
    (contDiffAt_fullContourMap hB m θ).of_le (by simp)
  have he : ∀ᶠ q in 𝓝 (0 : ShellContourParameters),
      DifferentiableAt ℝ (fullContourMap m B θ) q ∧ d q < d 0 + 1 := by
    filter_upwards [hc1.eventually (by norm_num),
      hd.eventually_lt continuousAt_const (lt_add_one (d 0))] with q hq hdq
    exact ⟨hq.differentiableAt (by norm_num), hdq⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r, d 0 + 1, hr, by exact add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one, ?_⟩
  intro q hq
  have hh := hball (by simpa only [dist_zero_right] using hq)
  exact ⟨hh.1, hh.2.le⟩

theorem fixedMassContourMap_injOn (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (τ : ℝ) :
    Set.InjOn (fixedMassContourMap m B θ τ)
      (fixedMassContourEmbedding τ ⁻¹' (fullContourLocalCoordinates m hB hθ).source) := by
  intro x hx y hy hxy
  change (fullContourMap m B θ (fixedMassContourEmbedding τ x), x.2) =
    (fullContourMap m B θ (fixedMassContourEmbedding τ y), y.2) at hxy
  have hf : fullContourLocalCoordinates m hB hθ (fixedMassContourEmbedding τ x) =
      fullContourLocalCoordinates m hB hθ (fixedMassContourEmbedding τ y) := by
    rw [fullContourLocalCoordinates_apply, fullContourLocalCoordinates_apply]
    change (fullContourMap m B θ (fixedMassContourEmbedding τ x), (τ, x.2)) =
      (fullContourMap m B θ (fixedMassContourEmbedding τ y), (τ, y.2))
    apply Prod.ext
    · exact congrArg (fun z : ShellPhysicalCoordinates => z.1) hxy
    · exact Prod.ext rfl (congrArg (fun z : ShellPhysicalCoordinates => z.2) hxy)
  have h := (fullContourLocalCoordinates m hB hθ).injOn hx hy hf
  exact Prod.ext (congrArg (fun q : ShellContourParameters => q.1) h)
    (congrArg (fun q : ShellContourParameters => q.2.2) h)

end VacuumBellSeparation

/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.RieszDomainCalculus
public import LeanPool.FastDynamo.Operator.RieszProjectionCalculus

/-!
# Commutation of the Riesz projection and its first spectral moment

The two-sided inverse equations for a bundled-domain resolvent imply that
ambient resolvents at two spectral parameters commute.  Moving this
pointwise identity through the operator-valued circle integral shows that the
first resolvent moment commutes with both every contour resolvent and the
Riesz projection.  Consequently the moment preserves the algebraic range of
the Riesz projection.

No idempotence or finite-rank assumption is needed for the range-invariance
statement.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S : Set ℂ} {c : ℂ} {R : ℝ}

omit [CompleteSpace X] in
/-- Ambient resolvents belonging to one chosen resolvent family commute.

This is an immediate algebraic consequence of the resolvent identity; it
does not require any contour or completeness hypothesis. -/
theorem stateResolvent_comm (h : HasResolventOn A S) {z w : ℂ}
    (hz : z ∈ S) (hw : w ∈ S) :
    (h.stateResolvent z).comp (h.stateResolvent w) =
      (h.stateResolvent w).comp (h.stateResolvent z) := by
  by_cases hzw : w = z
  · subst w
    rfl
  · calc
      (h.stateResolvent z).comp (h.stateResolvent w) =
          (w - z)⁻¹ • (h.stateResolvent z - h.stateResolvent w) :=
        h.stateResolvent_comp_eq_inv_smul_sub hz hw hzw
      _ = (z - w)⁻¹ •
          (h.stateResolvent w - h.stateResolvent z) := by
        rw [show z - w = -(w - z) by ring, inv_neg,
          show h.stateResolvent w - h.stateResolvent z =
            -(h.stateResolvent z - h.stateResolvent w) by abel]
        module
      _ = (h.stateResolvent w).comp (h.stateResolvent z) :=
        (h.stateResolvent_comp_eq_inv_smul_sub hw hz
          (fun h ↦ hzw h.symm)).symm

/-- A fixed contour resolvent commutes with the first normalized resolvent
moment. -/
theorem stateResolvent_comp_rieszSpectralMoment
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R)
    {z : ℂ} (hz : z ∈ sphere c R) :
    (h.stateResolvent z).comp h.rieszSpectralMoment =
      h.rieszSpectralMoment.comp (h.stateResolvent z) := by
  have hmomentInt : CircleIntegrable
      (fun q ↦ q • h.stateResolvent q) c R :=
    (continuousOn_id.smul h.continuousOn_stateResolvent).circleIntegrable hR
  have hpointwise : ∀ q ∈ sphere c R,
      (h.stateResolvent z).comp (q • h.stateResolvent q) =
        (q • h.stateResolvent q).comp (h.stateResolvent z) := by
    intro q hq
    calc
      (h.stateResolvent z).comp (q • h.stateResolvent q) =
          q • ((h.stateResolvent z).comp (h.stateResolvent q)) := by
        ext x
        simp
      _ = q • ((h.stateResolvent q).comp (h.stateResolvent z)) := by
        rw [h.stateResolvent_comm hz hq]
      _ = (q • h.stateResolvent q).comp (h.stateResolvent z) := by
        ext x
        simp
  unfold rieszSpectralMoment
  calc
    (h.stateResolvent z).comp
        ((2 * Real.pi * I : ℂ)⁻¹ •
          ∮ q in C(c, R), q • h.stateResolvent q) =
        (2 * Real.pi * I : ℂ)⁻¹ •
          (h.stateResolvent z).comp
            (∮ q in C(c, R), q • h.stateResolvent q) := by
      ext x
      simp
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
          (∮ q in C(c, R),
            (h.stateResolvent z).comp (q • h.stateResolvent q)) := by
      rw [circleIntegral_comp_left (h.stateResolvent z) hmomentInt]
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
          (∮ q in C(c, R),
            (q • h.stateResolvent q).comp (h.stateResolvent z)) := by
      congr 1
      apply circleIntegral.integral_congr hR
      exact hpointwise
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
          ((∮ q in C(c, R), q • h.stateResolvent q).comp
            (h.stateResolvent z)) := by
      rw [circleIntegral_comp_right hmomentInt]
    _ = ((2 * Real.pi * I : ℂ)⁻¹ •
          ∮ q in C(c, R), q • h.stateResolvent q).comp
            (h.stateResolvent z) := by
      ext x
      simp

/-- The Riesz projection commutes with the first normalized resolvent
moment. -/
theorem rieszProjection_comp_rieszSpectralMoment
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R) :
    h.rieszProjection.comp h.rieszSpectralMoment =
      h.rieszSpectralMoment.comp h.rieszProjection := by
  have hresInt : CircleIntegrable h.stateResolvent c R :=
    h.circleIntegrable_stateResolvent hR
  have hpointwise : ∀ z ∈ sphere c R,
      (h.stateResolvent z).comp h.rieszSpectralMoment =
        h.rieszSpectralMoment.comp (h.stateResolvent z) := by
    intro z hz
    exact h.stateResolvent_comp_rieszSpectralMoment hR hz
  unfold rieszProjection
  calc
    ((2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(c, R), h.stateResolvent z).comp
          h.rieszSpectralMoment =
        (2 * Real.pi * I : ℂ)⁻¹ •
          ((∮ z in C(c, R), h.stateResolvent z).comp
            h.rieszSpectralMoment) := by
      ext x
      simp
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
          (∮ z in C(c, R),
            (h.stateResolvent z).comp h.rieszSpectralMoment) := by
      rw [circleIntegral_comp_right hresInt]
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
          (∮ z in C(c, R),
            h.rieszSpectralMoment.comp (h.stateResolvent z)) := by
      congr 1
      apply circleIntegral.integral_congr hR
      exact hpointwise
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
          (h.rieszSpectralMoment.comp
            (∮ z in C(c, R), h.stateResolvent z)) := by
      rw [circleIntegral_comp_left h.rieszSpectralMoment hresInt]
    _ = h.rieszSpectralMoment.comp
          ((2 * Real.pi * I : ℂ)⁻¹ •
            ∮ z in C(c, R), h.stateResolvent z) := by
      ext x
      simp

/-- The first resolvent moment preserves the algebraic range of the Riesz
projection.  This is the public generic theorem used by the
finite-rank eigenmode extraction from the corrected-parametrix Riesz projection. -/
theorem rieszSpectralMoment_mem_rieszProjection_range
    (h : HasResolventOn A (sphere c R)) (hR : 0 ≤ R)
    {x : X} (hx : x ∈ h.rieszProjection.toLinearMap.range) :
    h.rieszSpectralMoment x ∈ h.rieszProjection.toLinearMap.range := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨h.rieszSpectralMoment y, ?_⟩
  have hcomm := congrArg (fun T : X →L[ℂ] X ↦ T y)
    (h.rieszProjection_comp_rieszSpectralMoment hR)
  change h.rieszProjection (h.rieszSpectralMoment y) =
    h.rieszSpectralMoment (h.rieszProjection y)
  simpa only [ContinuousLinearMap.comp_apply] using hcomm

end HasResolventOn

end

end FastDynamo

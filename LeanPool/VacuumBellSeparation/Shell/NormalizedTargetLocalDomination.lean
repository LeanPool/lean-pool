/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ActualInducedContourLocalBound
public import LeanPool.VacuumBellSeparation.Shell.NormalizedTargetCompact

/-!
# Genuine local contour patches cover the normalized target

The patch data below are constructed from the explicit proper future
Lorentz preimages and the actual local domination theorem. Their proof
fields record already proved facts; none are physical model assumptions.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ENNReal

/-- A Lorentz-frame neighborhood equipped with a uniform bound on the contour measure. -/
structure ControlledContourPatch (θ : ℝ) where
  /-- Lorentz frame used to describe the shell points in the patch. -/
  frame : Spacetime ≃L[ℝ] Spacetime
  proper : IsProperLorentzMap frame
  future : IsOrthochronousMap frame
  /-- Radius of the parameter polydisc used in the local estimate. -/
  radius : ℝ
  radius_pos : 0 < radius
  norm_bound : ∀ s : Fin 6 → ℝ, ‖s‖ ≤ radius →
    spacetimeEuclideanOperatorNorm (prefixedLorentzFamily frame s) < 32 / Real.sin θ ∧
    spacetimeEuclideanOperatorNorm (prefixedLorentzFamily frame s).symm < 32 / Real.sin θ
  /-- Open parameter neighborhood where the local shell estimate applies. -/
  neighborhood : Set (ℝ × ComplexSpacetime)
  isOpen_neighborhood : IsOpen neighborhood
  /-- Uniform comparison coefficient for the contour measure on the patch. -/
  coefficient : ℝ≥0∞
  coefficient_pos : 0 < coefficient
  coefficient_lt_top : coefficient < ∞
  integral_bound : ∀ t : ℝ, ∀ F : ComplexSpacetime → ℝ≥0∞, Measurable F →
    coefficient * (∫⁻ z in {z : complexShell t | (t, z.1) ∈ neighborhood},
      F z.1 ∂inducedRegularShellVolume t) ≤
      ∫⁻ y, physicalContourCutoffWeight t θ (32 / Real.sin θ) frame F y
        ∂(smoothBallProbability (Fin 6 → ℝ) radius radius_pos).prod (oneParticleMeasure t)

theorem normalizedTarget_exists_contourPatch {θ : ℝ} (hθ : 0 < Real.sin θ)
    {t : ℝ} {z : ComplexSpacetime} (hz : (t, z) ∈ normalizedTarget) :
    ∃ D : ControlledContourPatch θ, (t, z) ∈ D.neighborhood := by
  let p := normalizedTargetMomentum t z θ
  let B := p 1
  let Λ := normalizedTargetPreimageMap hz hθ
  have hB : 0 < B := normalizedTargetMomentum_transverse_pos hz hθ
  have hp : radialShellMomentum B 0 = p := by
    have ha := normalizedTargetMomentum_axis_coordinates t z θ
    ext i
    fin_cases i <;> simp [radialShellMomentum, B, p, ha.1, ha.2]
  have he : radialShellEnergy t B 0 < 32 / Real.sin θ := by
    rw [← radialShellMomentum_dispersion, hp]
    exact normalizedTargetMomentum_energy_lt hz hθ
  have hpoint : complexifiedSpacetimeMap Λ (radialShellContour t B θ 0) = z := by
    rw [radialShellContour_eq_boost, hp]
    exact normalizedTargetPreimageMap_boost hz hθ
  have hnorm := normalizedTargetPreimageMap_norm_lt hz hθ
  obtain ⟨ρ, hρ, hbound, V, hV, hcenter, k, hk, hkt, hint⟩ :=
    actualContour_induced_local_bound (normalizedTargetPreimageMap_isProper hz hθ).1
      t hB hθ he hnorm.1 hnorm.2
  refine ⟨{
    frame := Λ
    proper := normalizedTargetPreimageMap_isProper hz hθ
    future := normalizedTargetPreimageMap_isOrthochronous hz hθ
    radius := ρ
    radius_pos := hρ
    norm_bound := hbound
    neighborhood := V
    isOpen_neighborhood := hV
    coefficient := k
    coefficient_pos := hk
    coefficient_lt_top := hkt
    integral_bound := hint }, ?_⟩
  change (t, complexifiedSpacetimeMap Λ (radialShellContour t B θ 0)) ∈ V at hcenter
  rw [hpoint] at hcenter
  exact hcenter

theorem normalizedTarget_nonempty : normalizedTarget.Nonempty := by
  refine ⟨(0, (0, ![4, 4 * Complex.I, 0])), ?_⟩
  norm_num [normalizedTarget, complexShell, spatialDot, Fin.sum_univ_three,
    euclidSq, reLorentzSq, reSpatialSq, norm_mul, Complex.norm_I, Complex.I_sq,
    Complex.ext_iff, Complex.mul_re, Complex.mul_im, pow_two]

theorem normalizedTarget_finite_contourPatches {θ : ℝ} (hθ : 0 < Real.sin θ) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : Fin N → ControlledContourPatch θ,
      normalizedTarget ⊆ ⋃ i, (D i).neighborhood := by
  classical
  choose D hD using fun x : normalizedTarget => normalizedTarget_exists_contourPatch hθ x.2
  obtain ⟨s, hs⟩ := normalizedTarget_finite_subcover (fun x => (D x).neighborhood)
    (fun x => (D x).isOpen_neighborhood) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hD ⟨x, hx⟩⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := normalizedTarget_nonempty
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨his, _⟩ := mem_iUnion.mp hi
    exact ⟨i, his⟩
  let e := (Fintype.equivFin {i // i ∈ s}).symm
  refine ⟨Fintype.card {i // i ∈ s}, ?_, fun i => D (e i).1, ?_⟩
  · have : Nonempty {i // i ∈ s} := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
    exact Fintype.card_pos
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
    refine mem_iUnion.mpr ⟨e.symm ⟨i, his⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hxi

end VacuumBellSeparation

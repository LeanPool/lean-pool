/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellPatchMeasure
public import LeanPool.VacuumBellSeparation.Shell.CompatibleChartMeasureGluing

/-!
# The actual induced volume of a countable shell atlas

The global measure is built from actual Lorentz-transported charts and
their Euclidean Gram densities. All overlap compatibility hypotheses
of measure gluing are discharged. The measure is independent of the
countable atlas on the same covered open set. Coverage of an intended
region remains an explicit geometric statement, separate from any
nonlinear ambient Hausdorff area formula.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set

/-- Induced shell atlas domain. -/
def inducedShellAtlasDomain (m : ℝ) (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) :
    Set (complexShell m) := ⋃ n, inducedShellPatch m (Λ n)

/-- Induced shell atlas volume defined as `gluedChartMeasure (fun n => inducedShellPatch m (Λ n))
(fun n => inducedShellPatchVolume m (Λ n) (hΛ n))`. -/
noncomputable def inducedShellAtlasVolume (m : ℝ)
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ n, IsLorentzMap (Λ n)) :
    Measure (complexShell m) :=
  gluedChartMeasure (fun n => inducedShellPatch m (Λ n))
    (fun n => inducedShellPatchVolume m (Λ n) (hΛ n))

theorem isOpen_inducedShellAtlasDomain (m : ℝ)
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) : IsOpen (inducedShellAtlasDomain m Λ) :=
  isOpen_iUnion (fun n => isOpen_inducedShellPatch m (Λ n))

theorem inducedShellAtlasVolume_restrict_chart (m : ℝ)
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ n, IsLorentzMap (Λ n)) (n : ℕ) :
    (inducedShellAtlasVolume m Λ hΛ).restrict (inducedShellPatch m (Λ n)) =
      inducedShellPatchVolume m (Λ n) (hΛ n) :=
  gluedChartMeasure_restrict_patch _ _
    (fun n => (isOpen_inducedShellPatch m (Λ n)).measurableSet)
    (fun n => inducedShellPatchVolume_supported m (Λ n) (hΛ n))
    (fun i j => inducedShellPatchVolume_compatible m (Λ i) (Λ j) (hΛ i) (hΛ j)) n

theorem inducedShellAtlasVolume_supported (m : ℝ)
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ n, IsLorentzMap (Λ n)) :
    (inducedShellAtlasVolume m Λ hΛ).restrict (inducedShellAtlasDomain m Λ) =
      inducedShellAtlasVolume m Λ hΛ :=
  gluedChartMeasure_supported_union _ _
    (fun n => (isOpen_inducedShellPatch m (Λ n)).measurableSet)

/-- Restriction to any other actual chart is its Gram measure restricted
to the region covered by the atlas. The chart need not occur in the list. -/
theorem inducedShellAtlasVolume_restrict_other_chart (m : ℝ)
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ n, IsLorentzMap (Λ n))
    (Γ : Spacetime ≃L[ℝ] Spacetime) (hΓ : IsLorentzMap Γ) :
    (inducedShellAtlasVolume m Λ hΛ).restrict (inducedShellPatch m Γ) =
      (inducedShellPatchVolume m Γ hΓ).restrict (inducedShellAtlasDomain m Λ) := by
  let U : ℕ → Set (complexShell m) := fun n => inducedShellPatch m (Λ n)
  have hU : ∀ n, MeasurableSet (U n) :=
    fun n => (isOpen_inducedShellPatch m (Λ n)).measurableSet
  have hD : ∀ n, MeasurableSet (disjointed U n) := fun n => MeasurableSet.disjointed hU n
  have hterm (n : ℕ) :
      ((inducedShellPatchVolume m (Λ n) (hΛ n)).restrict (disjointed U n)).restrict
          (inducedShellPatch m Γ) =
        (inducedShellPatchVolume m Γ hΓ).restrict (disjointed U n) := by
    rw [Measure.restrict_restrict (isOpen_inducedShellPatch m Γ).measurableSet,
      inter_comm, ← Measure.restrict_restrict (hD n),
      inducedShellPatchVolume_compatible m (Λ n) Γ (hΛ n) hΓ,
      Measure.restrict_restrict_of_subset (disjointed_subset U n)]
  change (Measure.sum (fun n =>
    (inducedShellPatchVolume m (Λ n) (hΛ n)).restrict (disjointed U n))).restrict _ = _
  rw [Measure.restrict_sum _ (isOpen_inducedShellPatch m Γ).measurableSet]
  simp_rw [hterm]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) hD, iUnion_disjointed]
  rfl

theorem inducedShellAtlasVolume_restrict_covered_chart (m : ℝ)
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ n, IsLorentzMap (Λ n))
    (Γ : Spacetime ≃L[ℝ] Spacetime) (hΓ : IsLorentzMap Γ)
    (hsub : inducedShellPatch m Γ ⊆ inducedShellAtlasDomain m Λ) :
    (inducedShellAtlasVolume m Λ hΛ).restrict (inducedShellPatch m Γ) =
      inducedShellPatchVolume m Γ hΓ := by
  rw [inducedShellAtlasVolume_restrict_other_chart m Λ hΛ Γ hΓ]
  calc
    (inducedShellPatchVolume m Γ hΓ).restrict (inducedShellAtlasDomain m Λ) =
        ((inducedShellPatchVolume m Γ hΓ).restrict (inducedShellPatch m Γ)).restrict
          (inducedShellAtlasDomain m Λ) := by rw [inducedShellPatchVolume_supported]
    _ = inducedShellPatchVolume m Γ hΓ := by
      rw [Measure.restrict_restrict (isOpen_inducedShellAtlasDomain m Λ).measurableSet,
        inter_eq_right.mpr hsub, inducedShellPatchVolume_supported]

theorem inducedShellAtlasVolume_independent (m : ℝ)
    (Λ Γ : ℕ → Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ n, IsLorentzMap (Λ n)) (hΓ : ∀ n, IsLorentzMap (Γ n))
    (hregion : inducedShellAtlasDomain m Λ = inducedShellAtlasDomain m Γ) :
    inducedShellAtlasVolume m Λ hΛ = inducedShellAtlasVolume m Γ hΓ := by
  symm
  apply gluedChartMeasure_unique _ _
    (fun n => (isOpen_inducedShellPatch m (Λ n)).measurableSet)
    (fun n => inducedShellPatchVolume_supported m (Λ n) (hΛ n))
    (fun i j => inducedShellPatchVolume_compatible m (Λ i) (Λ j) (hΛ i) (hΛ j))
  · change (inducedShellAtlasVolume m Γ hΓ).restrict (inducedShellAtlasDomain m Λ) = _
    rw [hregion, inducedShellAtlasVolume_supported]
  · intro n
    apply inducedShellAtlasVolume_restrict_covered_chart
    rw [← hregion]
    exact subset_iUnion (fun n => inducedShellPatch m (Λ n)) n

theorem inducedShellAtlasVolume_apply_in_chart {m : ℝ}
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ n, IsLorentzMap (Λ n)) (n : ℕ)
    {s : Set (complexShell m)} (hs : MeasurableSet s)
    (hsub : s ⊆ inducedShellPatch m (Λ n)) :
    inducedShellAtlasVolume m Λ hΛ s = inducedShellCoordinateVolume m (Λ n)
      ((shellPatchPoint m (Λ n) (hΛ n) ⁻¹' s) ∩ euclideanShellChartDomain m) := by
  have h := congrArg (fun μ : Measure (complexShell m) => μ s)
    (inducedShellAtlasVolume_restrict_chart m Λ hΛ n)
  rw [Measure.restrict_apply hs, inter_eq_left.mpr hsub] at h
  exact h.trans (inducedShellPatchVolume_apply (Λ n) (hΛ n) hs)

end VacuumBellSeparation

/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.InducedShellAtlasVolume
public import LeanPool.VacuumBellSeparation.Shell.InducedShellChartCoverage
public import Mathlib.Topology.Bases
public import Mathlib.Data.Set.Countable

/-!
# A chart-independent Euclidean induced measure near the normalized target

Second countability selects an actual countable subatlas of the union
of regular Lorentz shell charts. Gluing their actual Gram measures
defines a measure on the original shell, supported on that open union.
Every normalized target belongs to the union.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set

/-- Shell Lorentz frame with underlying type `{Λ : Spacetime ≃L[ℝ] Spacetime // IsLorentzMap Λ}`. -/
abbrev ShellLorentzFrame := {Λ : Spacetime ≃L[ℝ] Spacetime // IsLorentzMap Λ}

/-- Regular shell region. -/
def regularShellRegion (m : ℝ) : Set (complexShell m) :=
  ⋃ Λ : ShellLorentzFrame, inducedShellPatch m Λ.1

theorem isOpen_regularShellRegion (m : ℝ) : IsOpen (regularShellRegion m) :=
  isOpen_iUnion (fun Λ => isOpen_inducedShellPatch m Λ.1)

theorem exists_countable_regularShellAtlas (m : ℝ) :
    ∃ Λ : ℕ → ShellLorentzFrame,
      inducedShellAtlasDomain m (fun n => (Λ n).1) = regularShellRegion m := by
  classical
  obtain ⟨s, hs, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun Λ : ShellLorentzFrame => inducedShellPatch m Λ.1)
    (fun Λ => isOpen_inducedShellPatch m Λ.1)
  let d : ShellLorentzFrame := ⟨ContinuousLinearEquiv.refl ℝ Spacetime, fun _ _ => rfl⟩
  let Λ : ℕ → ShellLorentzFrame := enumerateCountable hs d
  refine ⟨Λ, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨Λ n, hn⟩
  · intro z hz
    have hz' : z ∈ ⋃ L ∈ s, inducedShellPatch m L.1 := by
      rw [hcover]
      exact hz
    obtain ⟨L, hL⟩ := mem_iUnion.mp hz'
    obtain ⟨hLs, hzL⟩ := mem_iUnion.mp hL
    obtain ⟨n, hn⟩ := subset_range_enumerate hs d hLs
    exact mem_iUnion.mpr ⟨n, by simpa only [Λ, hn] using hzL⟩

/-- Regular shell atlas defined as `Classical.choose (exists_countable_regularShellAtlas m)`. -/
noncomputable def regularShellAtlas (m : ℝ) : ℕ → ShellLorentzFrame :=
  Classical.choose (exists_countable_regularShellAtlas m)

theorem regularShellAtlas_covers (m : ℝ) :
    inducedShellAtlasDomain m (fun n => (regularShellAtlas m n).1) = regularShellRegion m :=
  Classical.choose_spec (exists_countable_regularShellAtlas m)

/-- Induced regular shell volume defined as `inducedShellAtlasVolume m (fun n => (regularShellAtlas
m n).1) (fun n => (regularShellAtlas m n).2)`. -/
noncomputable def inducedRegularShellVolume (m : ℝ) : Measure (complexShell m) :=
  inducedShellAtlasVolume m (fun n => (regularShellAtlas m n).1)
    (fun n => (regularShellAtlas m n).2)

/-- Exact local formula for the global measure in every actual regular
chart, including charts outside the chosen countable list. -/
theorem inducedRegularShellVolume_restrict_chart (m : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ) :
    (inducedRegularShellVolume m).restrict (inducedShellPatch m Λ) =
      inducedShellPatchVolume m Λ hΛ := by
  apply inducedShellAtlasVolume_restrict_covered_chart
  rw [regularShellAtlas_covers]
  exact subset_iUnion (fun L : ShellLorentzFrame => inducedShellPatch m L.1) ⟨Λ, hΛ⟩

theorem inducedRegularShellVolume_supported (m : ℝ) :
    (inducedRegularShellVolume m).restrict (regularShellRegion m) =
      inducedRegularShellVolume m := by
  rw [← regularShellAtlas_covers]
  exact inducedShellAtlasVolume_supported _ _ _

theorem inducedRegularShellVolume_eq_any_atlas (m : ℝ)
    (Λ : ℕ → Spacetime ≃L[ℝ] Spacetime) (hΛ : ∀ n, IsLorentzMap (Λ n))
    (hcover : inducedShellAtlasDomain m Λ = regularShellRegion m) :
    inducedRegularShellVolume m = inducedShellAtlasVolume m Λ hΛ := by
  apply inducedShellAtlasVolume_independent
  exact (regularShellAtlas_covers m).trans hcover.symm

theorem inducedRegularShellVolume_apply_in_chart {m : ℝ}
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    {s : Set (complexShell m)} (hs : MeasurableSet s) (hsub : s ⊆ inducedShellPatch m Λ) :
    inducedRegularShellVolume m s = inducedShellCoordinateVolume m Λ
      ((shellPatchPoint m Λ hΛ ⁻¹' s) ∩ euclideanShellChartDomain m) := by
  have h := congrArg (fun μ : Measure (complexShell m) => μ s)
    (inducedRegularShellVolume_restrict_chart m Λ hΛ)
  rw [Measure.restrict_apply hs, inter_eq_left.mpr hsub] at h
  exact h.trans (inducedShellPatchVolume_apply Λ hΛ hs)

theorem normalizedTarget_mem_regularShellRegion {t : ℝ} {z : ComplexSpacetime}
    (hz : (t, z) ∈ normalizedTarget) :
    (⟨z, hz.2.2.1⟩ : complexShell t) ∈ regularShellRegion t := by
  obtain ⟨Λ, w, hΛ, _, hw, him, _, _⟩ :=
    normalizedTarget_volume_chart_coverage hz (θ := Real.pi / 2) (by simp)
  have hp : shellPatchPoint t Λ hΛ.1 w = (⟨z, hz.2.2.1⟩ : complexShell t) := by
    apply Subtype.ext
    apply complexSpacetimeEuclideanEquiv.injective
    exact him
  exact mem_iUnion.mpr ⟨⟨Λ, hΛ.1⟩, hp ▸ shellPatchPoint_mem Λ hΛ.1 hw⟩

end VacuumBellSeparation

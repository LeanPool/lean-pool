/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Geometry.CubeFaces
public import LeanPool.NairTenenbaum.Geometry.LipschitzBoundaryLatticeCount
public import LeanPool.NairTenenbaum.Geometry.NormLeOneRadialCharts

/-! # Lipschitz boundary charts and quantitative counting for the norm-one region

Restricting the smooth radial parametrizations to coordinate faces gives
finitely many charts with field-degree-minus-one parameters. The general
lattice-counting theorem applies after any real linear change of coordinates.
-/

@[expose] public section

open scoped NNReal Pointwise

namespace NairTenenbaum

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem fundamentalCone MeasureTheory

variable (K : Type*) [Field K] [NumberField K]

/-- The index set for the boundary charts of the norm region. -/
abbrev NormRegionBoundaryIndex :=
  ({w : InfinitePlace K // IsReal w} → Bool) × InfinitePlace K × Bool

open Classical in
/-- A chart covering one piece of the norm-region boundary. -/
noncomputable def normRegionBoundaryChart (j : NormRegionBoundaryIndex K)
    (v : Fin (Fintype.card (NormRegionParameter K) - 1) → ℝ) : mixedSpace K :=
  normRegionRadialChart K j.1 (cubeFaceMap (Sum.inl j.2.1) (if j.2.2 then 1 else 0) v)

open Classical in
theorem contDiff_normRegionBoundaryChart (j : NormRegionBoundaryIndex K) :
    ContDiff ℝ ⊤ (normRegionBoundaryChart K j) :=
  (contDiff_normRegionRadialChart K j.1).comp (contDiff_cubeFaceMap _ _)

open Classical in
theorem normLeOne_frontier_boundaryChart {x : mixedSpace K} (hx : x ∈ frontier (normLeOne K)) :
    ∃ j : NormRegionBoundaryIndex K,
      ∃ v : Fin (Fintype.card (NormRegionParameter K) - 1) → ℝ,
        v ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) ∧ normRegionBoundaryChart K j v = x := by
  obtain ⟨σ, v, hv, hchart, w, hw⟩ := normLeOne_frontier_radialChart K hx
  rcases hw with hzero | hone
  · obtain ⟨u, hu, heq⟩ := exists_cubeFaceMap_of_coordinate_eq hv hzero
    refine ⟨⟨σ, w, false⟩, u, hu, ?_⟩
    change normRegionRadialChart K σ (cubeFaceMap (Sum.inl w) 0 u) = x
    rw [heq, hchart]
  · obtain ⟨u, hu, heq⟩ := exists_cubeFaceMap_of_coordinate_eq hv hone
    refine ⟨⟨σ, w, true⟩, u, hu, ?_⟩
    change normRegionRadialChart K σ (cubeFaceMap (Sum.inl w) 1 u) = x
    rw [heq, hchart]

theorem exists_coordinate_normLeOne_lattice_error {ι : Type*} [Fintype ι]
    (e : mixedSpace K ≃L[ℝ] (ι → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      |(integerLatticeCount (t • (e '' normLeOne K)) : ℝ) -
        t ^ Fintype.card ι * volume.real (e '' normLeOne K)| ≤
        C * t ^ (Module.finrank ℚ K - 1) := by
  classical
  let f := fun j : NormRegionBoundaryIndex K => e ∘ normRegionBoundaryChart K j
  have hdiff (j : NormRegionBoundaryIndex K) : ContDiff ℝ ⊤ (f j) :=
    e.contDiff.comp (contDiff_normRegionBoundaryChart K j)
  choose L hL using fun j => (hdiff j).contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_Icc (fun _ => (0 : ℝ)) (fun _ => 1)) isCompact_Icc
  have hbounded : Bornology.IsBounded (e '' normLeOne K) :=
    e.toContinuousLinearMap.lipschitzWith.isBounded_image (isBounded_normLeOne K)
  have hcover : ∀ y ∈ frontier (e '' normLeOne K), ∃ j v,
      v ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) ∧ f j v = y := by
    intro y hy
    have HE : e '' frontier (normLeOne K) = frontier (e '' normLeOne K) :=
      e.toHomeomorph.image_frontier _
    rw [← HE] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨j, v, hv, heq⟩ := normLeOne_frontier_boundaryChart K hx
    exact ⟨j, v, hv, congrArg e heq⟩
  simpa only [Fintype.card_fin, card_normRegionParameter] using
    exists_lipschitz_boundary_lattice_discrepancy hbounded f L hL hcover

end NairTenenbaum

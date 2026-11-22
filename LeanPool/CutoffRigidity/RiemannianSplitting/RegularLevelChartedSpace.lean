/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RegularLevelLocalChart
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # A fixed-dimensional atlas on the actual regular level
Rank-nullity identifies the actual derivative kernels with a common model.
The resulting charts use the original zero-level subspace topology.
-/

@[expose] public section
open Bundle Set
open scoped Manifold ContDiff Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A surjective actual scalar derivative has a kernel of codimension one. -/
theorem finrank_ker_scalar_of_surjective (D : E →L[ℝ] ℝ)
    (hD : Function.Surjective D) :
    Module.finrank ℝ D.ker = Module.finrank ℝ E - 1 := by
  have hrank := D.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hD] at hrank
  have hrank' : 1 + Module.finrank ℝ D.ker = Module.finrank ℝ E := by
    simpa using hrank
  omega

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [RiemannianBundle fun x : M ↦ TangentSpace I x] in
/-- The actual zero-level charts may all be taken in one fixed Euclidean
model of dimension `dim M - 1`. -/
theorem exists_regularScalar_fixed_levelChart {f : M → ℝ} (x : {y : M // f y = 0})
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f x.val)
    (X : (y : M) → TangentSpace I y) (hne : mvfderiv I f x.val (X x.val) ≠ 0) :
    ∃ c : OpenPartialHomeomorph {y : M // f y = 0}
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))),
      x ∈ c.source ∧ c x = 0 := by
  obtain ⟨c, hc, hcz⟩ := exists_regularScalar_levelChart x hf X hne
  let D := fderiv ℝ (f ∘ (extChartAt I x.val).symm) (extChartAt I x.val x.val)
  have hdim : Module.finrank ℝ D.ker =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) := by
    rw [finrank_ker_scalar_of_surjective D
      (surjective_fderiv_chartScalar x.val (hf.mdifferentiableAt one_ne_zero) X hne)]
    simp
  let a : D.ker ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  refine ⟨c.trans a.toHomeomorph.toOpenPartialHomeomorph, ⟨hc, Set.mem_univ _⟩, ?_⟩
  change a (c x) = 0
  rw [hcz, map_zero]

/-- The actual regular level, with its original topology, admits the atlas
constructed above. Smooth compatibility is a separate obligation. -/
@[instance_reducible]
noncomputable def regularLevelChartedSpace {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (X : (y : M) → TangentSpace I y)
    (hregular : ∀ x, mvfderiv I f x (X x) ≠ 0) :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))) {y : M // f y = 0} := by
  classical
  let c := fun x : {y : M // f y = 0} ↦
    Classical.choose (exists_regularScalar_fixed_levelChart x (hf x.val) X (hregular x.val))
  exact
    { atlas := range c
      chartAt := c
      mem_chart_source := fun x ↦ (Classical.choose_spec
        (exists_regularScalar_fixed_levelChart x (hf x.val) X (hregular x.val))).1
      chart_mem_atlas := fun x ↦ ⟨x, rfl⟩ }

end CutoffRigidity

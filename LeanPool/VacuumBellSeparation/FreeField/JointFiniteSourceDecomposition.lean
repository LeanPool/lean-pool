/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointDifferenceCovariance
public import LeanPool.VacuumBellSeparation.FreeField.SourceInclusion
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # The actual regional decomposition of each original finite source -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian Matrix
open scoped InnerProductSpace

variable {μ s : ℝ} (hμ : 0 < μ)
  (S : Submodule ℝ TimeZeroSource) [FiniteDimensional ℝ S]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hμ S))
  (L R : Submodule ℝ (ι → ℝ)) (hLR : IsCompl L R)
  (hLA : ∀ x ∈ L, finiteSourceCoordinates hμ S b x ∈
    localizedTimeZeroSources (Metric.ball (jointCenterIndex s 0) 1))
  (hRB : ∀ x ∈ R, finiteSourceCoordinates hμ S b x ∈
    localizedTimeZeroSources (Metric.ball (jointCenterIndex s 1) 1))

/-- Joint projected source tests. -/
def jointProjectedSourceTests (i : ι) : Fin 2 → SourceTestSpace hμ (jointSourceRegion s) :=
  ![sourceTestInclusion hμ Set.subset_union_left (projectedFiniteSourceTest hμ S b L R hLR hLA i),
    sourceTestInclusion hμ Set.subset_union_right (projectedFiniteSourceTest hμ S b R L hLR.symm
      hRB i)]

omit [FiniteDimensional ℝ S] in
theorem jointProjectedSourceTests_localized (i : ι) (a : Fin 2) :
    (jointProjectedSourceTests hμ S b L R hLR hLA hRB i a).1 ∈
      localizedTimeZeroSources (Metric.ball (jointCenterIndex s a) 1) := by
  fin_cases a
  · exact hLA _ (Submodule.projection_apply_mem hLR _)
  · exact hRB _ (Submodule.projection_apply_mem hLR.symm _)

omit [FiniteDimensional ℝ S] in
theorem jointProjectedSourceTests_sum
    (hSU : S ≤ localizedTimeZeroSources (jointSourceRegion s)) (i : ι) :
    (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 0 : SourceHilbert hμ
      (jointSourceRegion s)) +
      (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 1 : SourceHilbert hμ
        (jointSourceRegion s)) =
        includedFiniteSourceFamily hμ S b hSU i := by
  have hp := DFunLike.congr_fun (Submodule.projection_add_projection_eq_id hLR) (Pi.single i 1)
  have hsum : L.projection R hLR (Pi.single i 1) + R.projection L hLR.symm (Pi.single i 1) =
      (Pi.single i 1 : ι → ℝ) := by
    simpa only [LinearMap.add_apply, LinearMap.id_apply] using hp
  have he : (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 0).1 +
      (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 1).1 = (b i).1 := by
    calc (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 0).1 +
          (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 1).1
        = finiteSourceCoordinates hμ S b (L.projection R hLR (Pi.single i 1)) +
          finiteSourceCoordinates hμ S b (R.projection L hLR.symm (Pi.single i 1)) := rfl
      _ = finiteSourceCoordinates hμ S b (Pi.single i 1) := by rw [← map_add, hsum]
      _ = (b i).1 := by
        have hb : b.equivFun.symm (Pi.single i 1) = b i := by
          apply b.equivFun.injective
          rw [LinearEquiv.apply_symm_apply]
          funext j
          rw [Module.Basis.equivFun_self, Pi.single_apply]
          by_cases h : j = i
          · subst h
            simp
          · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
        change (b.equivFun.symm (Pi.single i 1)).1 = (b i).1
        exact congrArg Subtype.val hb
  change _ = (finiteSourceTestInclusion hμ S hSU (b i) : SourceHilbert hμ (jointSourceRegion s))
  rw [← UniformSpace.Completion.coe_add]
  congr 1
  exact Subtype.ext he

omit [FiniteDimensional ℝ ↥S] in
theorem jointProjectedSourceTests_diagonal_gram (i j : ι) :
    inner ℝ (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 0 : SourceHilbert hμ
      (jointSourceRegion s))
        (jointProjectedSourceTests hμ S b L R hLR hLA hRB j 0 : SourceHilbert hμ
          (jointSourceRegion s)) +
      inner ℝ (jointProjectedSourceTests hμ S b L R hLR hLA hRB i 1 : SourceHilbert hμ
        (jointSourceRegion s))
        (jointProjectedSourceTests hμ S b L R hLR hLA hRB j 1 : SourceHilbert hμ
          (jointSourceRegion s)) =
      labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hμ S b) L R hLR i j := by
  rw [← congrFun (congrFun (finiteProductSourceFamily_gram hμ S b L R hLR hLA hRB) i) j]
  change _ = inner ℝ (finiteProductSourceFamily hμ S b L R hLR hLA hRB i)
    (finiteProductSourceFamily hμ S b L R hLR hLA hRB j)
  rw [finiteProductSourceFamily, finiteProductSourceFamily, WithLp.prod_inner_apply]
  change _ = inner ℝ (projectedFiniteSourceTest hμ S b L R hLR hLA i :
        SourceHilbert hμ (Metric.ball (jointCenterIndex s 0) 1))
      (projectedFiniteSourceTest hμ S b L R hLR hLA j :
        SourceHilbert hμ (Metric.ball (jointCenterIndex s 0) 1)) +
    inner ℝ (projectedFiniteSourceTest hμ S b R L hLR.symm hRB i :
        SourceHilbert hμ (Metric.ball (jointCenterIndex s 1) 1))
      (projectedFiniteSourceTest hμ S b R L hLR.symm hRB j :
        SourceHilbert hμ (Metric.ball (jointCenterIndex s 1) 1))
  simp only [sourceHilbert_test_inner_covariance]
  rfl

end VacuumBellSeparation

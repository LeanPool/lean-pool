/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityBounds
public import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry
public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityIntegrability
public import LeanPool.LiebThirring.Electrostatics.SlicingScreenedFaces
public import LeanPool.LiebThirring.Electrostatics.SlicingFaceIntegrals

/-!
# The distributional Laplacian of the screened potential

Equation with the explicit unordered genuine-face integrals.

Equation, stated directly with the face measure `ν`.
-/

public section

open Set MeasureTheory Laplacian
open scoped NNReal ContDiff

namespace LiebThirring

theorem integral_eq_sum_voronoiCells {M : ℕ} (hM : 1 ≤ M)
    (R : Fin M → Position) (hR : Function.Injective R)
    (g : Position → ℝ) (hg : Integrable g) :
    (∫ x, g x) = ∑ k : Fin M, ∫ x in voronoiCell R k, g x := by
  have ha : ∀ᵐ x : Position, x ∈ ⋃ k, voronoiCell R k := by
    apply ae_iff.mpr
    exact volume_compl_voronoiCells R hR (by omega)
  rw [integral_eq_setIntegral ha g]
  exact integral_iUnion_fintype (fun k => (isOpen_voronoiCell R k).measurableSet)
    (fun _ _ h => disjoint_voronoiCell R h) (fun _ => hg.integrableOn)

/-- Equation (8.2) with the explicit unordered genuine-face integrals. -/
theorem integral_screenedPotentialReal_mul_laplacian_faces {M : ℕ} (hM : 1 ≤ M)
    (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (f : Position → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, screenedPotentialReal Z R x * Δ f x) =
      -4 * Real.pi * ∑ p : NuclearPair M,
        ∫ x in voronoiFace R p.val.1 p.val.2,
          nuclearFaceDensity R (Z : ℝ) p.val.1 p.val.2 x * f x
            ∂bisectorSurfaceMeasure R hR p.val.1 p.val.2 (ne_of_lt p.property) := by
  rw [integral_eq_sum_voronoiCells hM R hR _
    (integrable_screenedPotentialReal_mul_laplacian hM Z R hR hf hfc)]
  simp_rw [integral_screenedPotentialReal_laplacian_voronoiCell Z R hR _ f hf hfc]
  let G : ∀ k l : Fin M, k ≠ l → ℝ := fun k l hkl =>
    ∫ x in voronoiFace R k l, screenedCellBoundaryTerm Z R k l f x
      ∂bisectorSurfaceMeasure R hR k l hkl
  rw [sum_directedNuclearPairs_oriented G, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ =>
    integral_screenedCellBoundaryTerm_pair Z R hR _ _ _ f hf hfc)

/-- Equation (8.2), stated directly with the face measure `ν`. -/
theorem integral_screenedPotentialReal_mul_laplacian {M : ℕ} (hM : 1 ≤ M)
    (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R)
    (f : Position → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x, screenedPotentialReal Z R x * Δ f x) =
      -4 * Real.pi * ∫ x, f x ∂voronoiFaceMeasure R hR (Z : ℝ) := by
  rw [integral_voronoiFaceMeasure_density R hR Z.coe_nonneg f
    (integrable_compact_voronoiFaceMeasure R hR Z.coe_nonneg hf.continuous hfc)]
  exact integral_screenedPotentialReal_mul_laplacian_faces hM Z R hR f hf hfc

end LiebThirring

end

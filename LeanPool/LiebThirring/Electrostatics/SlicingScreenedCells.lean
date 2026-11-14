/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.SlicingGreen
public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityExtension
public import LeanPool.LiebThirring.Electrostatics.SlicingJump

/-!
# The screened Green identity in each cell

The globally smooth extension agrees with the Coulomb representative near
its closed cell. Green's second identity therefore applies without any
singular field or unproved trace assumption.
-/

public section

open Set MeasureTheory InnerProductSpace Laplacian
open scoped NNReal ContDiff

namespace LiebThirring

/-- The screened-potential boundary contribution of a Voronoi cell in Green’s identity. -/
@[expose] noncomputable def screenedCellBoundaryTerm {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (k l : Fin M) (f : Position → ℝ) (x : Position) : ℝ :=
  screenedCellPotential Z R k x * fderiv ℝ f x (bisectorNormal R k l) -
    f x * fderiv ℝ (screenedCellPotential Z R k) x (bisectorNormal R k l)

theorem sum_slicingGreenComponent (g f : Position → ℝ) (n x : Position) :
    (∑ a : Fin 3, n a * slicingGreenComponent g f a x) =
      g x * fderiv ℝ f x n - f x * fderiv ℝ g x n := by
  unfold slicingGreenComponent
  have h₁ := sum_position_rankOne (fderiv ℝ f x) n
  have h₂ := sum_position_rankOne (fderiv ℝ g x) n
  calc
    _ = g x * (∑ a : Fin 3, fderiv ℝ f x (EuclideanSpace.basisFun (Fin 3) ℝ a) * n a) -
      f x * (∑ a : Fin 3, fderiv ℝ g x (EuclideanSpace.basisFun (Fin 3) ℝ a) * n a) := by
        simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    _ = _ := by rw [h₁, h₂]

theorem integrableOn_screenedCellBoundaryTerm {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k l : Fin M) (hkl : k ≠ l)
    (f : Position → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    IntegrableOn (screenedCellBoundaryTerm Z R k l f) (voronoiFace R k l)
      (bisectorSurfaceMeasure R hR k l hkl) := by
  classical
  let g := screenedCellSmooth Z R hR k
  have hg : ContDiff ℝ 2 g := (contDiff_screenedCellSmooth Z R hR k).of_le (by simp)
  have hi : IntegrableOn (fun x => ∑ a : Fin 3,
      bisectorNormal R k l a * slicingGreenComponent g f a x) (voronoiFace R k l)
      (bisectorSurfaceMeasure R hR k l hkl) := by
    apply integrable_finsetSum
    intro a _
    exact ((integrable_compact_bisectorSurfaceMeasure R hR k l hkl _
      (contDiff_slicingGreenComponent hg hf a).continuous
      (hasCompactSupport_slicingGreenComponent hfc a)).const_mul _).integrableOn
  apply hi.congr_fun _ (measurableSet_voronoiFace R k l)
  intro x hx
  have he := eventuallyEq_screenedCellSmooth Z R hR k (voronoiFace_subset_closed R k l hx)
  dsimp only
  rw [sum_slicingGreenComponent g f (bisectorNormal R k l) x]
  dsimp only [g]
  rw [he.eq_of_nhds, he.fderiv_eq]
  rfl

/-- The harmonic bulk term vanishes; only the directed screened face term remains. -/
theorem integral_screenedPotentialReal_laplacian_voronoiCell {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    (f : Position → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x in voronoiCell R k, screenedPotentialReal Z R x * Δ f x) =
      ∑ l : {l : Fin M // l ≠ k}, ∫ x in voronoiFace R k l.val,
        screenedCellBoundaryTerm Z R k l.val f x
          ∂bisectorSurfaceMeasure R hR k l.val l.property.symm := by
  classical
  let g := screenedCellSmooth Z R hR k
  have hg : ContDiff ℝ 2 g := (contDiff_screenedCellSmooth Z R hR k).of_le (by simp)
  have he := voronoiCell_compact_green R hR k g f hg hf hfc
  have hleft : (∫ x in voronoiCell R k, g x * Δ f x - f x * Δ g x) =
      ∫ x in voronoiCell R k, screenedPotentialReal Z R x * Δ f x := by
    apply setIntegral_congr_fun (isOpen_voronoiCell R k).measurableSet
    intro x hx
    have hc := voronoiCell_subset_closed R k hx
    have hs := eventuallyEq_screenedCellSmooth Z R hR k hc
    have hharm := (harmonicAt_screenedCellPotential Z R hR k hc).2
    dsimp only [g]
    rw [(laplacian_congr_nhds hs).eq_of_nhds, hharm.eq_of_nhds, Pi.zero_apply, mul_zero, sub_zero,
      hs.eq_of_nhds,
      ← screenedPotentialReal_eq_screenedCellPotential Z R hR k hc]
  rw [hleft] at he
  apply he.trans
  apply Finset.sum_congr rfl
  intro l _
  apply setIntegral_congr_fun (measurableSet_voronoiFace R k l.val)
  intro x hx
  have hs := eventuallyEq_screenedCellSmooth Z R hR k (voronoiFace_subset_closed R k l.val hx)
  dsimp only
  rw [sum_slicingGreenComponent g f (bisectorNormal R k l.val) x]
  dsimp only [g]
  rw [hs.eq_of_nhds, hs.fderiv_eq]
  rfl

end LiebThirring

end

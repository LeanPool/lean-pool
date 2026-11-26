/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! True weighted Euclidean least-squares residuals for DRE8 (3.5), §§6–7.
No independence/nonzero-weight hypothesis is required: the finite-dimensional
subspace projection also covers degenerate moment families. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
variable {n : ℕ}

/-- Weighted modal power with the Euclidean L² norm, never the Pi sup norm. -/
def momentVector (a t : Fin n → ℝ) (p : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => a i * t i ^ p)

@[simp] theorem momentVector_apply (a t : Fin n → ℝ) (p : ℕ) (i : Fin n) :
    momentVector a t p i = a i * t i ^ p := rfl

/-- Exactly the source span of the first three weighted modal moments. -/
def quadraticMomentSpace (a t : Fin n → ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ {momentVector a t 0, momentVector a t 1, momentVector a t 2}

/-- A general weighted quadratic, with all three real coefficients explicit. -/
def quadraticVector (a t : Fin n → ℝ) (c0 c1 c2 : ℝ) : EuclideanSpace ℝ (Fin n) :=
  c0 • momentVector a t 0 + c1 • momentVector a t 1 + c2 • momentVector a t 2

@[simp] theorem quadraticVector_apply (a t : Fin n → ℝ) (c0 c1 c2 : ℝ) (i : Fin n) :
    quadraticVector a t c0 c1 c2 i = a i * (c0 + c1 * t i + c2 * t i ^ 2) := by
  simp [quadraticVector, momentVector]
  ring

theorem quadraticVector_mem (a t : Fin n → ℝ) (c0 c1 c2 : ℝ) :
    quadraticVector a t c0 c1 c2 ∈ quadraticMomentSpace a t := by
  exact Submodule.mem_span_triple.mpr ⟨c0,c1,c2,rfl⟩

/-- The actual orthogonal residual, defined without any supplied minimizer. -/
def projectionResidual (a t : Fin n → ℝ) (p : ℕ) : EuclideanSpace ℝ (Fin n) :=
  momentVector a t p - (quadraticMomentSpace a t).starProjection (momentVector a t p)

/-- The source κ_p: norm of the true orthogonal residual. -/
def kappa (a t : Fin n → ℝ) (p : ℕ) : ℝ := ‖projectionResidual a t p‖

@[simp] theorem kappa_nonneg (a t : Fin n → ℝ) (p : ℕ) : 0 ≤ kappa a t p :=
  norm_nonneg _

/-- κ_p is literally the distance to the source quadratic-moment subspace. -/
theorem kappa_eq_infDist (a t : Fin n → ℝ) (p : ℕ) :
    kappa a t p = Metric.infDist (momentVector a t p) (quadraticMomentSpace a t) := by
  simpa only [kappa, projectionResidual, dist_eq_norm] using
    (quadraticMomentSpace a t).dist_starProjection_eq_infDist (momentVector a t p)

/-- Projection lies in the span, hence genuine coefficients always exist,
even if the three moment vectors are linearly dependent. -/
theorem exists_projection_coefficients (a t : Fin n → ℝ) (p : ℕ) :
    ∃ c0 c1 c2 : ℝ,
      quadraticVector a t c0 c1 c2 =
        (quadraticMomentSpace a t).starProjection (momentVector a t p) := by
  exact Submodule.mem_span_triple.mp
    ((quadraticMomentSpace a t).starProjection_apply_mem (momentVector a t p))

/-- Pointwise attained residual coefficients; no projection certificate is a premise. -/
theorem exists_projection_residual_coefficients (a t : Fin n → ℝ) (p : ℕ) :
    ∃ c0 c1 c2 : ℝ, ∀ i,
      projectionResidual a t p i = a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2)) := by
  obtain ⟨c0,c1,c2,hc⟩ := exists_projection_coefficients a t p
  refine ⟨c0,c1,c2,fun i => ?_⟩
  simp only [projectionResidual, ← hc, PiLp.sub_apply, momentVector_apply,
    quadraticVector_apply]
  ring

/-- Exact finite-coordinate L² norm bridge. -/
theorem kappa_sq_eq_sum (a t : Fin n → ℝ) (p : ℕ) :
    kappa a t p ^ 2 = ∑ i, projectionResidual a t p i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- An attained weighted polynomial least-squares objective, valid for all p. -/
theorem exists_kappa_coefficients (a t : Fin n → ℝ) (p : ℕ) :
    ∃ c0 c1 c2 : ℝ,
      (∑ i, (a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2))) ^ 2) = kappa a t p ^ 2 := by
  obtain ⟨c0,c1,c2,hc⟩ := exists_projection_residual_coefficients a t p
  refine ⟨c0,c1,c2,?_⟩
  rw [kappa_sq_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i]

/-- The actual projection is no farther than every explicit quadratic. -/
theorem kappa_le_quadratic_residual (a t : Fin n → ℝ) (p : ℕ) (c0 c1 c2 : ℝ) :
    kappa a t p ≤ ‖momentVector a t p - quadraticVector a t c0 c1 c2‖ := by
  rw [kappa_eq_infDist]
  simpa only [dist_eq_norm] using
    (Metric.infDist_le_dist_of_mem (x := momentVector a t p)
      (quadraticVector_mem a t c0 c1 c2))

/-- Full global minimality against every coefficient triple, in literal sums. -/
theorem kappa_sq_le_quadratic_residual (a t : Fin n → ℝ) (p : ℕ) (c0 c1 c2 : ℝ) :
    kappa a t p ^ 2 ≤ ∑ i, (a i * (t i ^ p-(c0 + c1 * t i + c2 * t i ^ 2))) ^ 2 := by
  have h := pow_le_pow_left₀ (kappa_nonneg a t p)
    (kappa_le_quadratic_residual a t p c0 c1 c2) 2
  rw [EuclideanSpace.real_norm_sq_eq] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PiLp.sub_apply, momentVector_apply, quadraticVector_apply]
  ring

/-- Residual is orthogonal to the full source moment span. -/
theorem projectionResidual_orthogonal (a t : Fin n → ℝ) (p : ℕ) :
    projectionResidual a t p ∈ (quadraticMomentSpace a t)ᗮ :=
  (quadraticMomentSpace a t).sub_starProjection_mem_orthogonal _

end C145DRE8

end

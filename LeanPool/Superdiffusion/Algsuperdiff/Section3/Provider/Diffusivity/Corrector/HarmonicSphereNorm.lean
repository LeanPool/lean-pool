/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Euclidean
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# HarmonicSphereNorm

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Euclidean norm on the sup-normed carrier, and its coordinate calculus

`Vec d = Fin d -> R` carries the **sup** norm, so Mathlib's `‖·‖` on the
carrier is not the Euclidean gauge in which spheres, radial functions and the
Laplacian are written.  CoarseGraining supplies the squared Euclidean gauge
`vecNormSq` and the explicit balls `euclideanBall`/`euclideanClosedBall` built
from it, but no norm and no differential calculus for it.

This module adds the norm `euclideanNorm x = sqrt (vecNormSq x)`, its
elementary comparison with the explicit balls, and -- the substantive part --
the coordinate derivative of a function of the Euclidean distance to a fixed
centre.  The derivative is expressed through `coordFDeriv`, the continuous linear
functional `v ↦ sum_i c i * v i`, which is the only shape of Frechet derivative
that occurs for the functions considered here and which evaluates on
CoarseGraining's `basisVec i` to `c i`.

Everything is carrier-native: no `EuclideanSpace` transfer appears anywhere,
and CoarseGraining's `euclideanCoordDeriv i u x = fderiv R u x (basisVec i)` is
used as the definition of the coordinate derivative throughout.

## Contents

* `euclideanNorm`, `sq_euclideanNorm`, `euclideanNorm_pos`,
  `continuous_euclideanNorm` -- the norm and its basic properties.
* `mem_euclideanBall_iff_euclideanNorm_lt`,
  `mem_euclideanClosedBall_iff_euclideanNorm_le` -- the explicit balls in terms
  of the norm.
* `coord, `coord -- the coordinate functionals.
* `has, `has, `has -- the derivative of the Euclidean gauge away from its
  centre.
* `has, `euclideanCoordDeriv_comp_euclideanNorm_sub` -- the chain rule `d_i
  (Phi (|x - z|)) = Phi' (|x - z|) * (x i - z i) / |x - z|`.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The Euclidean norm expressed through the squared vector norm. -/
noncomputable def euclideanNorm (x : Vec d) : ℝ := Real.sqrt (vecNormSq x)

theorem euclideanNorm_nonneg (x : Vec d) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

theorem sq_euclideanNorm (x : Vec d) : euclideanNorm x ^ 2 = vecNormSq x :=
  Real.sq_sqrt (vecNormSq_nonneg x)

theorem euclideanNorm_eq_zero_iff {x : Vec d} : euclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    refine vecNormSq_eq_zero ?_
    have := sq_euclideanNorm x
    rw [h] at this
    simpa using this.symm
  · intro h
    simp [euclideanNorm, h, vecNormSq, vecDot]

theorem euclideanNorm_pos {x : Vec d} (hx : x ≠ 0) : 0 < euclideanNorm x :=
  lt_of_le_of_ne (euclideanNorm_nonneg x) fun h => hx (euclideanNorm_eq_zero_iff.mp h.symm)

theorem continuous_vecNormSq : Continuous (vecNormSq : Vec d → ℝ) := by
  unfold vecNormSq vecDot
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

theorem continuous_euclideanNorm : Continuous (euclideanNorm : Vec d → ℝ) :=
  Real.continuous_sqrt.comp continuous_vecNormSq

theorem euclideanSqDist_eq_sq_euclideanNorm (x y : Vec d) :
    euclideanSqDist x y = euclideanNorm (x - y) ^ 2 := by
  rw [sq_euclideanNorm]
  rfl

theorem mem_euclideanBall_iff_euclideanNorm_lt {z x : Vec d} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ euclideanBall z r ↔ euclideanNorm (x - z) < r := by
  have hn := euclideanNorm_nonneg (x - z)
  change euclideanSqDist x z < r ^ 2 ↔ _
  rw [euclideanSqDist_eq_sq_euclideanNorm]
  constructor <;> intro h <;> nlinarith

theorem mem_euclideanClosedBall_iff_euclideanNorm_le {z x : Vec d} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ euclideanClosedBall z r ↔ euclideanNorm (x - z) ≤ r := by
  have hn := euclideanNorm_nonneg (x - z)
  change euclideanSqDist x z ≤ r ^ 2 ↔ _
  rw [euclideanSqDist_eq_sq_euclideanNorm]
  constructor <;> intro h <;> nlinarith

/-- The continuous linear functional with coordinate coefficient vector `c`. -/
noncomputable def coordFDeriv (c : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, c i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

@[simp] theorem coordFDeriv_apply (c v : Vec d) : coordFDeriv c v = ∑ i : Fin d, c i * v i := by
  simp [coordFDeriv]

/-- The derivative of the squared Euclidean norm. -/
theorem hasFDerivAt_vecNormSq (x : Vec d) :
    HasFDerivAt (vecNormSq : Vec d → ℝ)
      (coordFDeriv (fun i => 2 * x i)) x := by
  have key : ∀ i : Fin d, HasFDerivAt (fun y : Vec d => y i * y i)
      ((2 * x i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)) x := by
    intro i
    have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt (x := x)
    have hmul := h.mul h
    refine hmul.congr_fderiv ?_
    ext v
    simp [two_mul, add_mul]
  have hres := HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) => key i)
  have hfun : (∑ i : Fin d, fun y : Vec d => y i * y i) = (vecNormSq : Vec d → ℝ) := by
    funext y
    simp [vecNormSq, vecDot, Finset.sum_apply]
  rw [hfun] at hres
  exact hres


theorem euclideanCoordDeriv_of_hasFDerivAt {f : Vec d → ℝ} {L : Vec d →L[ℝ] ℝ} {x : Vec d}
    (h : HasFDerivAt f L x) (i : Fin d) : euclideanCoordDeriv i f x = L (basisVec i) := by
  rw [euclideanCoordDeriv, h.fderiv]

theorem hasFDerivAt_vecNormSq_sub (z x : Vec d) :
    HasFDerivAt (fun y : Vec d => vecNormSq (y - z))
      (coordFDeriv (fun i => 2 * (x i - z i))) x := by
  have h1 : HasFDerivAt (fun y : Vec d => y - z) (ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).sub_const z
  have h2 := (hasFDerivAt_vecNormSq (x - z)).comp x h1
  refine h2.congr_fderiv ?_
  ext v
  simp

theorem hasFDerivAt_euclideanNorm_sub {z x : Vec d} (hx : x ≠ z) :
    HasFDerivAt (fun y : Vec d => euclideanNorm (y - z))
      (coordFDeriv (fun i => (x i - z i) / euclideanNorm (x - z))) x := by
  have hne : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hNpos : 0 < euclideanNorm (x - z) := euclideanNorm_pos hne
  have hq : vecNormSq (x - z) ≠ 0 := fun h => hne (vecNormSq_eq_zero h)
  have hsqrt := Real.hasDerivAt_sqrt hq
  have hcomp := hsqrt.comp_hasFDerivAt x (hasFDerivAt_vecNormSq_sub z x)
  refine hcomp.congr_fderiv ?_
  ext v
  have hN : Real.sqrt (vecNormSq (x - z)) = euclideanNorm (x - z) := rfl
  simp only [smul_apply, coordFDeriv_apply, smul_eq_mul, hN,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hNne : euclideanNorm (x - z) ≠ 0 := ne_of_gt hNpos
  field_simp

theorem hasFDerivAt_comp_euclideanNorm_sub {Φ : ℝ → ℝ} {c : ℝ} {z x : Vec d}
    (hx : x ≠ z) (hΦ : HasDerivAt Φ c (euclideanNorm (x - z))) :
    HasFDerivAt (fun y : Vec d => Φ (euclideanNorm (y - z)))
      (coordFDeriv (fun i => c * ((x i - z i) / euclideanNorm (x - z)))) x := by
  have hcomp := hΦ.comp_hasFDerivAt x (hasFDerivAt_euclideanNorm_sub hx)
  refine hcomp.congr_fderiv ?_
  ext v
  simp [Finset.mul_sum, mul_assoc]

theorem euclideanCoordDeriv_comp_euclideanNorm_sub {Φ : ℝ → ℝ} {c : ℝ} {z x : Vec d}
    (hx : x ≠ z) (hΦ : HasDerivAt Φ c (euclideanNorm (x - z))) (i : Fin d) :
    euclideanCoordDeriv i (fun y : Vec d => Φ (euclideanNorm (y - z))) x =
      c * ((x i - z i) / euclideanNorm (x - z)) := by
  rw [euclideanCoordDeriv_of_hasFDerivAt (hasFDerivAt_comp_euclideanNorm_sub hx hΦ) i]
  simp


theorem hasFDerivAt_coord_sub {z x : Vec d} (i : Fin d) :
    HasFDerivAt (fun y : Vec d => y i - z i) (coordFDeriv (basisVec i)) x := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt
    (x := x)).sub_const (z i)
  refine h.congr_fderiv ?_
  ext v
  simp

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector

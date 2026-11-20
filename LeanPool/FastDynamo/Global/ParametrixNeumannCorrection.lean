/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.ResolventAnnulus
public import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Parametrix-to-Riesz transfer

This file isolates the reusable operator algebra in the global parametrix
argument.  A continuous domain-valued parametrix is corrected pointwise by a
Neumann inverse of its right error (`correctedInverse`), which is a right inverse of the pencil
when the right error has norm `< 1`.  If the pencil is moreover Fredholm of index zero, the
corrected right inverse is two-sided and gives a resolvent family
(`hasResolventOnOfRightParametrixIndexZero`).  The geometric-series bound and the identity
`(1+E)⁻¹ - 1 = -(1+E)⁻¹E` for the correction prepare the comparison of the state resolvent
with the uncorrected state parametrix, and a pointwise comparison integrates around a circle to
the estimate `‖Q - (2πi)⁻¹∮ ι R‖ ≤ r C` (`norm_rieszProjection_sub_contourOperator_le`).

The test of spectral nontriviality on one nonzero vector (`ne_zero_of_inner_contour_test`) is
in `Global/HorizontalSpectralExtraction.lean`; the true-resolvent error bound is
`TorusGlobalRieszNonzero.norm_stateResolvent_sub_stateParametrix_le_of_inv`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex MeasureTheory Metric Set

namespace ParametrixNeumannCorrection

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]

/-! ## Parametrix errors and the Neumann correction -/

/-- The ambient right error of a domain-valued parametrix. -/
def rightError (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (z : ℂ) : X →L[ℂ] X :=
  (A.pencil z).comp (R z) - ContinuousLinearMap.id ℂ X

/-- The right correction `1 + E`, equal to the pencil composed with the
parametrix. -/
def rightCorrection (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (z : ℂ) : X →L[ℂ] X :=
  ContinuousLinearMap.id ℂ X + rightError A R z

/-- The Neumann-corrected domain-valued inverse. -/
def correctedInverse (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (z : ℂ) : X →L[ℂ] D :=
  (R z).comp (Ring.inverse (rightCorrection A R z))

omit [CompleteSpace X] [CompleteSpace D] in
/-- The right correction `1 + E_right` is exactly the pencil composed with the parametrix,
`(z - A) ∘ R z`. -/
theorem rightCorrection_eq_pencil_comp
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D) (z : ℂ) :
    rightCorrection A R z = (A.pencil z).comp (R z) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [rightCorrection, rightError, add_apply, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  abel

omit [CompleteSpace D] in
/-- If the right error has norm `< 1` then the right correction is invertible, by the Neumann
series. -/
theorem isUnit_rightCorrection_of_norm_lt_one
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D) (z : ℂ)
    (hsmall : ‖rightError A R z‖ < 1) : IsUnit (rightCorrection A R z) := by
  change IsUnit (1 + rightError A R z)
  rw [← sub_neg_eq_add]
  exact isUnit_one_sub_of_norm_lt_one (by simpa using hsmall)

omit [CompleteSpace D] in
/-- The Neumann-corrected parametrix is a right inverse of the pencil whenever the right error has
norm `< 1`. -/
theorem correctedInverse_right_inv
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D) (z : ℂ)
    (hsmall : ‖rightError A R z‖ < 1) :
    (A.pencil z).comp (correctedInverse A R z) =
      ContinuousLinearMap.id ℂ X := by
  rw [correctedInverse, ← ContinuousLinearMap.comp_assoc,
    ← rightCorrection_eq_pencil_comp A R z]
  change rightCorrection A R z * Ring.inverse (rightCorrection A R z) = 1
  exact Ring.mul_inverse_cancel _
    (isUnit_rightCorrection_of_norm_lt_one A R z hsmall)

/-! ## A contour resolver from a continuous parametrix -/

omit [CompleteSpace X] [CompleteSpace D] in
/-- The right error depends continuously on the spectral parameter wherever the parametrix does,
the pencil being continuous in `z`. -/
theorem continuousOn_rightError {S : Set ℂ}
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (hR : ContinuousOn R S) : ContinuousOn (rightError A R) S := by
  unfold rightError
  exact A.continuous_pencil.continuousOn.clm_comp hR |>.sub continuousOn_const

omit [CompleteSpace X] [CompleteSpace D] in
/-- A surjective Fredholm pencil of algebraic index zero is injective.  This
is the abstract bridge used when the paper supplies only a right
parametrix identity and obtains index zero from elliptic Fredholm theory. -/
theorem pencil_injective_of_isFredholm_index_zero_of_surjective
    (T : D →L[ℂ] X) (hFred : ContinuousLinearMap.IsFredholm T)
    (hindex : T.toLinearMap.index = 0) (hsurj : Function.Surjective T) :
    Function.Injective T := by
  have : FiniteDimensional ℂ T.ker := hFred.finite_ker
  have hfinZ : (Module.finrank ℂ T.ker : ℤ) = 0 := by
    rw [← T.toLinearMap.index_of_surjective hsurj]
    exact hindex
  have hfin : Module.finrank ℂ T.ker = 0 := by
    exact_mod_cast hfinZ
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.finrank_eq_zero.mp hfin

/-- A resolvent family from a right parametrix, in the form used by the paper: the small
right error produces surjectivity, while a separately proved Fredholm
index-zero statement supplies injectivity. -/
def hasResolventOnOfRightParametrixIndexZero {S : Set ℂ}
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (hR : ContinuousOn R S)
    (hright : ∀ z ∈ S, ‖rightError A R z‖ < 1)
    (hFred : ∀ z ∈ S, ContinuousLinearMap.IsFredholm (A.pencil z))
    (hindex : ∀ z ∈ S, (A.pencil z).toLinearMap.index = 0) :
    HasResolventOn A S where
  inv := correctedInverse A R
  right_inv z hz := correctedInverse_right_inv A R z (hright z hz)
  left_inv := by
    intro z hz
    apply ContinuousLinearMap.ext
    intro d
    have hsurj : Function.Surjective (A.pencil z) := by
      intro x
      refine ⟨correctedInverse A R z x, ?_⟩
      have hx := DFunLike.congr_fun
        (correctedInverse_right_inv A R z (hright z hz)) x
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using hx
    apply pencil_injective_of_isFredholm_index_zero_of_surjective
      (A.pencil z) (hFred z hz) (hindex z hz) hsurj
    have hrightApply := DFunLike.congr_fun
      (correctedInverse_right_inv A R z (hright z hz)) ((A.pencil z) d)
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hrightApply
  continuousOn := by
    intro z hz
    have hcorr : ContinuousWithinAt (rightCorrection A R) S z := by
      exact (continuousOn_const.add (continuousOn_rightError A R hR)) z hz
    have hinv : ContinuousWithinAt
        (fun w ↦ Ring.inverse (rightCorrection A R w)) S z := by
      have hu := isUnit_rightCorrection_of_norm_lt_one A R z (hright z hz)
      have hinvAt : ContinuousAt Ring.inverse (rightCorrection A R z) := by
        simpa only [hu.unit_spec] using
          (NormedRing.inverse_continuousAt hu.unit)
      simpa only [Function.comp_def] using
        hinvAt.comp_continuousWithinAt hcorr
    exact (hR z hz).clm_comp hinv

/-! ## The state parametrix and the inverse of the correction -/

/-- The ambient operator obtained by embedding the output of the
domain-valued parametrix. -/
def stateParametrix (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (z : ℂ) : X →L[ℂ] X :=
  A.embedding.comp (R z)

omit [CompleteSpace D] in
/-- Sharp geometric-series bound for the inverse of the right correction. -/
theorem norm_ringInverse_rightCorrection_le
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D) (z : ℂ)
    (hsmall : ‖rightError A R z‖ < 1) :
    ‖Ring.inverse (rightCorrection A R z)‖ ≤
      (1 - ‖rightError A R z‖)⁻¹ := by
  let E := rightError A R z
  have hneg : ‖-E‖ < 1 := by simpa only [norm_neg] using hsmall
  change ‖Ring.inverse (1 + E)‖ ≤ (1 - ‖E‖)⁻¹
  rw [← sub_neg_eq_add, ← geom_series_eq_inverse (-E) hneg]
  calc
    ‖∑' n : ℕ, (-E) ^ n‖ ≤
        ‖(1 : X →L[ℂ] X)‖ - 1 + (1 - ‖-E‖)⁻¹ :=
      tsum_geometric_le_of_norm_lt_one (-E) hneg
    _ ≤ (1 - ‖E‖)⁻¹ := by
      have hid : ‖(1 : X →L[ℂ] X)‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le
      rw [norm_neg]
      linarith

omit [CompleteSpace D] in
/-- Exact resolvent-correction error identity used in the paper:
`(1+E)^{-1}-1 = -(1+E)^{-1}E`. -/
theorem ringInverse_rightCorrection_sub_id
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D) (z : ℂ)
    (hsmall : ‖rightError A R z‖ < 1) :
    Ring.inverse (rightCorrection A R z) - ContinuousLinearMap.id ℂ X =
      -(Ring.inverse (rightCorrection A R z)).comp (rightError A R z) := by
  let C := rightCorrection A R z
  let E := rightError A R z
  have hunit : IsUnit C :=
    isUnit_rightCorrection_of_norm_lt_one A R z hsmall
  have hcancel : Ring.inverse C * C = (1 : X →L[ℂ] X) :=
    Ring.inverse_mul_cancel C hunit
  change Ring.inverse C - 1 = -(Ring.inverse C) * E
  have hC : C = 1 + E := rfl
  calc
    Ring.inverse C - 1 = Ring.inverse C - Ring.inverse C * C := by
      rw [hcancel]
    _ = -(Ring.inverse C) * E := by
      rw [hC]
      noncomm_ring

/-! ## Integration around the contour -/

omit [CompleteSpace X] [CompleteSpace D] in
/-- The ambient state parametrix `A.embedding ∘ R z` is continuous in `z` wherever the parametrix
is; this is what allows integrating it around the contour. -/
theorem continuousOn_stateParametrix {S : Set ℂ}
    (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (hR : ContinuousOn R S) : ContinuousOn (stateParametrix A R) S := by
  unfold stateParametrix
  exact continuousOn_const.clm_comp hR

/-- The normalized contour operator of an approximate state resolvent.  It
need not itself be idempotent. -/
def contourOperator (A : DomainOperator X D) (R : ℂ → X →L[ℂ] D)
    (c : ℂ) (r : ℝ) : X →L[ℂ] X :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    circleIntegral (stateParametrix A R) c r

omit [CompleteSpace X] [CompleteSpace D] in
/-- A pointwise state-resolvent/parametrix bound integrates to the sharp
radius-times-bound estimate for normalized contour operators. -/
theorem norm_rieszProjection_sub_contourOperator_le
    {A : DomainOperator X D} {c : ℂ} {r C : ℝ} (hr : 0 ≤ r)
    (h : HasResolventOn A (sphere c r))
    (R : ℂ → X →L[ℂ] D) (hR : ContinuousOn R (sphere c r))
    (hbound : ∀ z ∈ sphere c r,
      ‖h.stateResolvent z - stateParametrix A R z‖ ≤ C) :
    ‖h.rieszProjection - contourOperator A R c r‖ ≤ r * C := by
  have hParamInt : CircleIntegrable (stateParametrix A R) c r :=
    (continuousOn_stateParametrix A R hR).circleIntegrable hr
  rw [HasResolventOn.rieszProjection, contourOperator, ← smul_sub]
  rw [← circleIntegral.integral_sub
    (h.circleIntegrable_stateResolvent hr) hParamInt]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    hr hbound

end ParametrixNeumannCorrection

end

end FastDynamo

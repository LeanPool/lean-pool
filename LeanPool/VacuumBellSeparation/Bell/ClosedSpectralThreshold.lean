/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.SpectralThreshold
public import LeanPool.VacuumBellSeparation.Bell.ReflectionApprox
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
The actual closed upper spectral cut: 1 minus the range projection of
the positive part of u I - A. Thus eigenvectors at the threshold are
included, unlike the existing strict upper cut of A - u I.
Only scalar matrix elements are integrated; operator-norm Bochner
measurability of the projection family is not assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral projection of a self-adjoint operator onto the closed upper interval at the
threshold. -/
def closedThresholdProjection (A : H →L[ℂ] H) (u : ℝ) : H →L[ℂ] H :=
  1 - thresholdProjection (-A) (-u)

theorem closedThresholdProjection_eq (A : H →L[ℂ] H) (u : ℝ) :
    closedThresholdProjection A u =
      1 - rangeProjection (((u : ℂ) • (1 : H →L[ℂ] H) - A)⁺) := by
  have he : -A - ((-u : ℝ) : ℂ) • (1 : H →L[ℂ] H) =
      (u : ℂ) • (1 : H →L[ℂ] H) - A := by
    rw [Complex.ofReal_neg, neg_smul]
    abel
  rw [closedThresholdProjection, thresholdProjection, he]

theorem closedThresholdProjection_mem (M : VonNeumannAlgebra H)
    {A : H →L[ℂ] H} (hA : A ∈ M) (u : ℝ) : closedThresholdProjection A u ∈ M :=
  sub_mem (one_mem M) (thresholdProjection_mem M (neg_mem hA) (-u))

theorem closedThresholdProjection_isSelfAdjoint (A : H →L[ℂ] H) (u : ℝ) :
    IsSelfAdjoint (closedThresholdProjection A u) :=
  ReflectionApprox.isSelfAdjoint_one_op.sub (thresholdProjection_isSelfAdjoint (-A) (-u))

theorem closedThresholdProjection_idem (A : H →L[ℂ] H) (u : ℝ) :
    closedThresholdProjection A u * closedThresholdProjection A u =
      closedThresholdProjection A u := by
  simp only [closedThresholdProjection, mul_sub, sub_mul, one_mul, mul_one,
    thresholdProjection_idem]
  abel

theorem closedThresholdProjection_commute_self {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (u : ℝ) :
    closedThresholdProjection A u * A = A * closedThresholdProjection A u := by
  have h := thresholdProjection_commute_self hA.neg (-u)
  have hc : thresholdProjection (-A) (-u) * A = A * thresholdProjection (-A) (-u) := by
    simpa only [mul_neg, neg_mul, neg_inj] using h
  simp only [closedThresholdProjection, sub_mul, mul_sub, one_mul, mul_one, hc]

theorem sub_mul_closedThresholdProjection_isPositive {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (u : ℝ) :
    ((A - (u : ℂ) • (1 : H →L[ℂ] H)) * closedThresholdProjection A u).IsPositive := by
  have he : ((-u : ℝ) : ℂ) • (1 : H →L[ℂ] H) - -A =
      A - (u : ℂ) • (1 : H →L[ℂ] H) := by
    rw [Complex.ofReal_neg, neg_smul]
    abel
  simpa only [closedThresholdProjection, he] using
    sub_mul_one_sub_thresholdProjection_isPositive hA.neg (-u)

theorem sub_mul_one_sub_closedThresholdProjection_isPositive {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (u : ℝ) :
    (((u : ℂ) • (1 : H →L[ℂ] H) - A) * (1 - closedThresholdProjection A u)).IsPositive := by
  have he : -A - ((-u : ℝ) : ℂ) • (1 : H →L[ℂ] H) =
      (u : ℂ) • (1 : H →L[ℂ] H) - A := by
    rw [Complex.ofReal_neg, neg_smul]
    abel
  simpa only [closedThresholdProjection, sub_sub_cancel, he] using
    sub_mul_thresholdProjection_isPositive hA.neg (-u)

theorem closedThresholdProjection_mul_of_le {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) {u v : ℝ} (huv : u ≤ v) :
    closedThresholdProjection A u * closedThresholdProjection A v =
      closedThresholdProjection A v := by
  have h := thresholdProjection_mul_of_le hA.neg (neg_le_neg huv)
  have hs := congrArg star h
  rw [star_mul, (thresholdProjection_isSelfAdjoint (-A) (-u)).star_eq,
    (thresholdProjection_isSelfAdjoint (-A) (-v)).star_eq] at hs
  simp only [closedThresholdProjection, mul_sub, sub_mul, one_mul, mul_one, hs]
  abel

theorem closedThresholdProjection_sub_isPositive {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) {u v : ℝ} (huv : u ≤ v) :
    (closedThresholdProjection A u - closedThresholdProjection A v).IsPositive := by
  have hpq := closedThresholdProjection_mul_of_le hA huv
  have hqp := congrArg star hpq
  rw [star_mul, (closedThresholdProjection_isSelfAdjoint A u).star_eq,
    (closedThresholdProjection_isSelfAdjoint A v).star_eq] at hqp
  apply isPositive_of_isSelfAdjoint_of_idem
    ((closedThresholdProjection_isSelfAdjoint A u).sub
      (closedThresholdProjection_isSelfAdjoint A v))
  simp only [mul_sub, sub_mul, closedThresholdProjection_idem, hpq, hqp]
  abel

/-- Quadratic form of the closed spectral projection evaluated at a vector. -/
def closedThresholdQuadratic (A : H →L[ℂ] H) (x : H) (u : ℝ) : ℝ :=
  (⟪x, closedThresholdProjection A u x⟫_ℂ).re

theorem closedThresholdQuadratic_nonneg (A : H →L[ℂ] H) (x : H) (u : ℝ) :
    0 ≤ closedThresholdQuadratic A x u :=
  (isPositive_of_isSelfAdjoint_of_idem
    (closedThresholdProjection_isSelfAdjoint A u)
    (closedThresholdProjection_idem A u)).re_inner_nonneg_right x

theorem closedThresholdQuadratic_le (A : H →L[ℂ] H) (x : H) (u : ℝ) :
    closedThresholdQuadratic A x u ≤ ‖x‖ ^ 2 := by
  have hp := (ReflectionApprox.isPositive_one_sub_of_isSelfAdjoint_of_idem
    (closedThresholdProjection_isSelfAdjoint A u)
    (closedThresholdProjection_idem A u)).re_inner_nonneg_right x
  simpa only [closedThresholdQuadratic, RCLike.re_eq_complex_re, sub_apply,
    one_apply_eq_self, inner_sub_right, Complex.sub_re,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re, sub_nonneg] using hp

theorem closedThresholdQuadratic_antitone {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (x : H) : Antitone (closedThresholdQuadratic A x) := by
  intro u v huv
  have hp := (closedThresholdProjection_sub_isPositive hA huv).re_inner_nonneg_right x
  simpa only [closedThresholdQuadratic, RCLike.re_eq_complex_re, sub_apply,
    inner_sub_right, Complex.sub_re, sub_nonneg] using hp

theorem closedThresholdQuadratic_intervalIntegrable {A : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (x : H) (a b : ℝ) :
    IntervalIntegrable (closedThresholdQuadratic A x) volume a b :=
  (closedThresholdQuadratic_antitone hA x).intervalIntegrable

/-- Self-adjoint unitary associated with the closed spectral projection. -/
def spectralReflection (A : H →L[ℂ] H) (u : ℝ) : H →L[ℂ] H :=
  (2 : ℂ) • closedThresholdProjection A u - 1

theorem spectralReflection_mem (M : VonNeumannAlgebra H) {A : H →L[ℂ] H}
    (hA : A ∈ M) (u : ℝ) : spectralReflection A u ∈ reflections M :=
  two_smul_sub_one_mem_reflections (closedThresholdProjection_mem M hA u)
    (closedThresholdProjection_isSelfAdjoint A u) (closedThresholdProjection_idem A u)

end VacuumBellSeparation

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorAnchoredMean
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.Geometry
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeBesovPoincare.W12LocalPoincare

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorAnchoredMeanTelescope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Successive centered-cube mean control

This module isolates the one-step estimate needed to telescope the means of a
fixed-unit-normalized corrector.  Its volume loss is dimension-only because
only a parent cube and its central child are compared.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The scale-correct oscillation quantity controlling the jump from the `n`th
centered-cube mean to the `(n+1)`st mean. -/
@[expose]
noncomputable def anchoredCorrectorMeanStepBound
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) : ℝ :=
  ((3 ^ d : ℕ) : ℝ) *
    cubeBesovOscillation (originCube d ((n + 1 : ℕ) : ℤ)) (2 : ℝ≥0∞)
      (z.localH1Function (n + 1)).toFun

/-- Restricting a normalized `L²` norm from an origin cube to its central
child costs at most the number of triadic children. -/
theorem cubeLpNorm_originCube_pred_le_card_mul
    {d : ℕ} (k : ℤ) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k))) :
    cubeLpNorm (originCube d (k - 1)) (2 : ℝ≥0∞) f ≤
      ((3 ^ d : ℕ) : ℝ) *
        cubeLpNorm (originCube d k) (2 : ℝ≥0∞) f := by
  have hraw :=
    CubeCalderonZygmund.eLpNorm_centralDescendant_le_descendantCount_mul
      (originCube d k) 1 FiniteLpExponent.two f
  rw [centralDescendant_originCube_eq_originCube_sub] at hraw
  have htop :
      ENNReal.ofReal (((3 ^ d) ^ 1 : ℕ) : ℝ) *
          eLpNorm f 2 (normalizedCubeMeasure (originCube d k)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  simpa [cubeLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    Nat.cast_nonneg] using hreal

/-- The averages on a centered cube and its central child differ by at most a
dimension-only multiple of the parent's normalized `L²` oscillation. -/
theorem abs_cubeAverage_originCube_pred_sub_le_card_mul_oscillation
    {d : ℕ} (k : ℤ) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k))) :
    |cubeAverage (originCube d (k - 1)) f -
        cubeAverage (originCube d k) f| ≤
      ((3 ^ d : ℕ) : ℝ) *
        cubeBesovOscillation (originCube d k) (2 : ℝ≥0∞) f := by
  have hchild : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (k - 1))) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp 1 hf
    simpa only [centralDescendant_originCube_eq_originCube_sub] using! h
  have hfluct : MemLp (cubeFluctuation (originCube d k) f) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k)) :=
    hf.sub (memLp_const _)
  have havg :
      cubeAverage (originCube d (k - 1))
          (cubeFluctuation (originCube d k) f) =
        cubeAverage (originCube d (k - 1)) f -
          cubeAverage (originCube d k) f := by
    have hfluct_eq : cubeFluctuation (originCube d k) f =
        fun x => f x - cubeAverage (originCube d k) f :=
      funext fun x => cubeFluctuation_apply (originCube d k) f x
    rw [hfluct_eq]
    exact cubeAverage_sub_const_of_memLp_two (originCube d (k - 1)) hchild
      (cubeAverage (originCube d k) f)
  calc
    |cubeAverage (originCube d (k - 1)) f -
        cubeAverage (originCube d k) f| =
        ‖cubeAverage (originCube d (k - 1))
          (cubeFluctuation (originCube d k) f)‖ := by
            rw [havg]
            exact (Real.norm_eq_abs _).symm
    _ ≤ cubeLpNorm (originCube d (k - 1)) (2 : ℝ≥0∞)
          (cubeFluctuation (originCube d k) f) :=
      norm_cubeAverage_le_cubeLpNorm_two _ _ (by
        have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp 1 hfluct
        simpa only [centralDescendant_originCube_eq_originCube_sub] using! h)
    _ ≤ ((3 ^ d : ℕ) : ℝ) *
        cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
          (cubeFluctuation (originCube d k) f) :=
      cubeLpNorm_originCube_pred_le_card_mul k _ hfluct
    _ = ((3 ^ d : ℕ) : ℝ) *
        cubeBesovOscillation (originCube d k) (2 : ℝ≥0∞) f := rfl

/-- Successive averages of the global corrector representative satisfy the
same one-step oscillation estimate, read through the outer canonical local
`H¹` representative. -/
theorem NormalizedLocalH1Carrier.abs_cubeAverage_globalValueRepresentative_succ_sub_le_oscillation
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    |cubeAverage (originCube d (n : ℤ)) z.globalValueRepresentative -
        cubeAverage (originCube d ((n + 1 : ℕ) : ℤ))
          z.globalValueRepresentative| ≤
      anchoredCorrectorMeanStepBound z n := by
  rw [z.cubeAverage_globalValueRepresentative_eq_localH1Function n,
    z.cubeAverage_globalValueRepresentative_eq_localH1Function (n + 1)]
  rw [← z.cubeAverage_localH1Function_eq_of_le (Nat.le_succ n)]
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Nat.succ_eq_add_one, anchoredCorrectorMeanStepBound] using
    abs_cubeAverage_originCube_pred_sub_le_card_mul_oscillation
      ((n : ℤ) + 1) (z.localH1Function (n + 1)).toFun
      (z.localH1Function (n + 1)).memL2_normalizedCubeMeasure

/-- The displacement of the outer mean from the unit-cube mean is bounded by
the finite sum of the scale-correct one-step oscillation quantities. -/
theorem NormalizedLocalH1Carrier.abs_cubeAverage_globalValueRepresentative_zero_sub_le_sum
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    |cubeAverage (originCube d 0) z.globalValueRepresentative -
        cubeAverage (originCube d (n : ℤ)) z.globalValueRepresentative| ≤
      ∑ k ∈ Finset.range n, anchoredCorrectorMeanStepBound z k := by
  let A : ℕ → ℝ := fun k =>
    cubeAverage (originCube d (k : ℤ)) z.globalValueRepresentative
  have htel : ∑ k ∈ Finset.range n, (A (k + 1) - A k) = A n - A 0 :=
    Finset.sum_range_sub A n
  calc
    |cubeAverage (originCube d 0) z.globalValueRepresentative -
        cubeAverage (originCube d (n : ℤ)) z.globalValueRepresentative| =
        |∑ k ∈ Finset.range n, (A (k + 1) - A k)| := by
          rw [htel]
          simp only [A]
          exact abs_sub_comm _ _
    _ ≤ ∑ k ∈ Finset.range n, |A (k + 1) - A k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, anchoredCorrectorMeanStepBound z k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_sub_comm]
      exact z.abs_cubeAverage_globalValueRepresentative_succ_sub_le_oscillation k

/-- Fixed-unit normalization turns the finite telescope into a direct bound
for the absolute outer mean. -/
theorem NormalizedLocalH1Carrier.abs_cubeAverage_globalValueRepresentative_le_sum
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    |cubeAverage (originCube d (n : ℤ)) z.globalValueRepresentative| ≤
      ∑ k ∈ Finset.range n, anchoredCorrectorMeanStepBound z k := by
  have h := z.abs_cubeAverage_globalValueRepresentative_zero_sub_le_sum n
  rw [z.cubeAverage_globalValueRepresentative_zero, zero_sub, abs_neg] at h
  exact h

end

end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4Bounds

/-!
# P4Moments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Moment transport for cutoff coarse ellipticity

This module assembles law-level moment consequences of the verified samplewise
cutoff bounds.  It deliberately keeps the deterministic lower moment separate
from the stochastic upper moment, whose proof must consume the actual Γ₂
control of the cutoff local envelope.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ} [NeZero d]

/-- All finite lower `(P4)` moments are integrable under the genuine cutoff law.  This
uses only the deterministic coercivity `nu`; it introduces no upper-ellipticity
or structural-law hypothesis. -/
theorem integrable_lambdaSqCoeffField_inv_pow_cutoffLaw
    (M : ABKModel d) (m : ℤ) (Q : TriadicCube d) {s : ℝ} (hs : 0 < s)
    (xi : ℕ) :
    Integrable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) ^ xi)
      (coefficientCutoffLaw M m) := by
  let P := coefficientCutoffLaw M m
  let f : CutoffSample d → RegCoeffField d := coefficientCutoff M.nu m
  let C : ℝ := 4 * (d : ℝ) * M.nu⁻¹
  let hP : Ch04.RestrictionLawCarrier P := coefficientCutoffLaw_lawCarrier M m
  have htarget_ae : AEMeasurable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) ^ xi) P :=
    (hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q hs).pow_const xi
  change Integrable (fun a : RegCoeffField d =>
      ((Ch04.lambdaSqCoeffField Q s (.finite 1) a)⁻¹) ^ xi) P
  rw [show P = Measure.map f (cutoffSampleLaw M).toMeasure by
    exact coefficientCutoffLaw_eq_map M m]
  apply (integrable_map_measure htarget_ae.aestronglyMeasurable
    (measurable_coefficientCutoff M.nu m).aemeasurable).mpr
  refine Integrable.mono' (integrable_const (C ^ xi))
    (htarget_ae.comp_aemeasurable (measurable_coefficientCutoff M.nu m).aemeasurable).aestronglyMeasurable ?_
  filter_upwards with omega
  have hbase_nonneg : 0 ≤
      (Ch04.lambdaSqCoeffField Q s (.finite 1) (f omega))⁻¹ := by
    exact inv_nonneg.mpr (Ch04.lambdaSqCoeffField_finite_nonneg Q (f omega) hs (by norm_num))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le d))
      (inv_nonneg.mpr M.nu_pos.le)
  have hbound : (Ch04.lambdaSqCoeffField Q s (.finite 1) (f omega))⁻¹ ≤ C := by
    exact lambdaSqCoeffField_inv_le_cutoffCoercivity M m omega Q hs
  have hpow : (Ch04.lambdaSqCoeffField Q s (.finite 1) (f omega))⁻¹ ^ xi ≤ C ^ xi :=
    pow_le_pow_left₀ hbase_nonneg hbound xi
  simpa only [Function.comp_apply, f, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hbase_nonneg xi),
    abs_of_nonneg (pow_nonneg hC_nonneg xi)] using hpow

end

end Algsuperdiff.Section3.Cutoff

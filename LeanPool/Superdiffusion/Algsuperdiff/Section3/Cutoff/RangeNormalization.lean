/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientLocality
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CutoffSampleRange
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RangeDependence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Law
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Annealed.RestrictionBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.DilationLaw

/-!
# RangeNormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Canonical normalization of the cutoff range

The cutoff at scale `m` has literal range `sqrt(d) * 3^m`.  We use the fixed
open-thickening budget `epsilon = 1/4` and normalize by the *least* triadic
depth whose spatial factor leaves strict room for the two thickenings.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport MeasureTheory Metric ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions
open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-- Fixed open-thickening radius used in the local-integral to restriction
bridge.  Its exact value leaves the slack `1 - 2 epsilon = 1/2`. -/
def cutoffBridgeEpsilon : ℝ := 1 / 4

theorem cutoffBridgeEpsilon_pos : 0 < cutoffBridgeEpsilon := by
  norm_num [cutoffBridgeEpsilon]

@[simp] theorem one_sub_two_mul_cutoffBridgeEpsilon :
    1 - 2 * cutoffBridgeEpsilon = 1 / 2 := by
  norm_num [cutoffBridgeEpsilon]

theorem exists_cutoffNormalizationDepth (d : ℕ) (m : ℤ) :
    ∃ k : ℕ, 2 * cutoffNaturalRange d m < (3 : ℝ) ^ k := by
  exact pow_unbounded_of_one_lt _ (by norm_num)

/-- Least triadic depth that leaves strict `epsilon = 1/4` bridge slack for
the literal cutoff range.  This is a deterministic natural number, never a
noncanonical choice witness. -/
noncomputable def cutoffNormalizationDepth (d : ℕ) (m : ℤ) : ℕ :=
  Nat.find (exists_cutoffNormalizationDepth d m)

theorem cutoffNormalizationDepth_spec (d : ℕ) (m : ℤ) :
    2 * cutoffNaturalRange d m < (3 : ℝ) ^ cutoffNormalizationDepth d m :=
  Nat.find_spec (exists_cutoffNormalizationDepth d m)

/-- Exact strict slack discharged by the canonical depth. -/
theorem cutoffNormalizationDepth_strict_slack (d : ℕ) (m : ℤ) :
    cutoffNaturalRange d m < (3 : ℝ) ^ cutoffNormalizationDepth d m *
      (1 - 2 * cutoffBridgeEpsilon) := by
  rw [one_sub_two_mul_cutoffBridgeEpsilon]
  nlinarith [cutoffNormalizationDepth_spec d m]

private theorem continuous_coefficientCutoff_entry (nu : ℝ) (m : ℤ)
    (omega : CutoffSample d) (i j : Fin d) :
    Continuous (fun x : Vec d => coefficientCutoff nu m omega x i j) := by
  simpa only [coefficientCutoff_apply, Matrix.add_apply, Matrix.smul_apply] using!
    (continuous_const.add (continuous_cutoff_entry m omega i j))

/-- The canonical triadically normalized actual cutoff law has CoarseGraining's
exact unit-range dependence predicate. -/
theorem cutoffNormalization_unitRangeDependentLaw (M : ABKModel d) (m : ℤ) :
    HCPolySupport.Book.Ch04.RestrictionUnitRangeDependentLaw
      (HCPolySupport.Book.Ch04.restrictionScaleNormalizedLaw
        (cutoffNormalizationDepth d m)
        (coefficientCutoffLaw M m)) := by
  intro U V hU hV hUV
  let k : ℕ := cutoffNormalizationDepth d m
  let r : ℝ := (3 : ℝ) ^ k
  let S : Set (Vec d) := thickening cutoffBridgeEpsilon U
  let T : Set (Vec d) := thickening cutoffBridgeEpsilon V
  have hr : r ≠ 0 := by
    dsimp [r]
    positivity
  have hS : MeasurableSet S := isOpen_thickening.measurableSet
  have hT : MeasurableSet T := isOpen_thickening.measurableSet
  have hrS : MeasurableSet (r • S) := hS.const_smul_of_ne_zero hr
  have hrT : MeasurableSet (r • T) := hT.const_smul_of_ne_zero hr
  have hsep : ∀ ⦃x y : Vec d⦄, x ∈ r • S → y ∈ r • T →
      cutoffNaturalRange d m ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
    intro x y hx hy
    have hrpos : 0 < r := by dsimp [r]; positivity
    exact (Algsuperdiff.Section3.Annealed.lt_vecNorm_sub_of_mem_scaled_thickenings hrpos hUV
      (by simpa [r, k] using cutoffNormalizationDepth_strict_slack d m) hx hy).le
  let A : CutoffSample d → RegCoeffField d :=
    fun omega => rescaleReg k (coefficientCutoff M.nu m omega)
  have hAmeas : Measurable A :=
    (measurable_rescaleReg k).comp (measurable_coefficientCutoff M.nu m)
  have hAcont : ∀ omega i j, Continuous (fun x : Vec d => A omega x i j) := by
    intro omega i j
    exact (continuous_coefficientCutoff_entry M.nu m omega i j).comp
      (continuous_id.const_smul ((3 : ℝ) ^ k))
  have hlocalSource := indep_cutoffSampleLocalSigma_of_indep_completion M m (r • S) (r • T)
    (indep_lowerShellLocalCompletion_of_cutoff_separation M m hrS hrT hsep)
  have hA_local_S : @Measurable (CutoffSample d) (RegCoeffField d)
      (cutoffSampleLocalSigma M m (r • S)) (LocalSigmaR S) A := by
    exact (measurable_smulReg_local r hr S).comp
      (measurable_coefficientCutoff_local M m (r • S))
  have hA_local_T : @Measurable (CutoffSample d) (RegCoeffField d)
      (cutoffSampleLocalSigma M m (r • T)) (LocalSigmaR T) A := by
    exact (measurable_smulReg_local r hr T).comp
      (measurable_coefficientCutoff_local M m (r • T))
  have hlocal : Indep (MeasurableSpace.comap A (LocalSigmaR S))
      (MeasurableSpace.comap A (LocalSigmaR T)) (cutoffSampleLaw M).toMeasure :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hlocalSource hA_local_S.comap_le)
      hA_local_T.comap_le
  have hbridge :=
    Algsuperdiff.Section3.Annealed.indep_restrictionSigmaR_map_of_indep_localSigmaR_thickenings
    A hAmeas hAcont U V hU hV cutoffBridgeEpsilon cutoffBridgeEpsilon_pos hlocal
  have hmap : Measure.map A (cutoffSampleLaw M).toMeasure =
      HCPolySupport.Book.Ch04.restrictionScaleNormalizedLaw k
        (coefficientCutoffLaw M m) := by
    rw [HCPolySupport.Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg,
      coefficientCutoffLaw_eq_map]
    exact (Measure.map_map (measurable_rescaleReg k)
      (measurable_coefficientCutoff M.nu m)).symm
  simpa [A, k, S, T] using hmap ▸ hbridge

end

end Algsuperdiff.Section3.Cutoff

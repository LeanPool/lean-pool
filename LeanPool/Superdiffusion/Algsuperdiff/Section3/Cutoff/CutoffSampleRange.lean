/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LowerShellRange
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LocalLimit

/-!
# CutoffSampleRange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Transfer of lower-stream independence to the genuine cutoff carrier

The cutoff carrier is a full-measure subtype.  This module transfers completed
lower-stream independence to it using Borel local representatives, so no
unjustified claim that a completion is contained in the ambient Borel sigma
field is needed.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport MeasureTheory ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

private theorem ae_preimage_cutoffSampleLaw (M : ABKModel d) {s t : Set (ShellSeq d)}
    (hst : s =ᵐ[M.P.toMeasure] t) :
    (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' s =ᵐ[(cutoffSampleLaw M).toMeasure]
      (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' t := by
  rw [← map_cutoffSampleLaw_val M] at hst
  exact (Measure.tendsto_ae_map measurable_subtype_coe.aemeasurable).eventually hst

private theorem measure_preimage_cutoffSampleLaw (M : ABKModel d)
    {s : Set (ShellSeq d)} (hs : MeasurableSet s) :
    (cutoffSampleLaw M).toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' s) =
      M.P.toMeasure s := by
  rw [← Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable hs,
    map_cutoffSampleLaw_val]

/-- A.e.-completed lower-stream independence descends faithfully to the
full-measure cutoff subtype. -/
theorem indep_cutoffSampleLocalSigma_of_indep_completion (M : ABKModel d) (m : ℤ)
    (U V : Set (Vec d))
    (h : Indep (lowerShellLocalCompletion M m U) (lowerShellLocalCompletion M m V)
      M.P.toMeasure) :
    Indep (cutoffSampleLocalSigma M m U) (cutoffSampleLocalSigma M m V)
      (cutoffSampleLaw M).toMeasure := by
  rw [Indep_iff]
  intro s t hs ht
  rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨s', hs', rfl⟩
  rcases MeasurableSpace.measurableSet_comap.1 ht with ⟨t', ht', rfl⟩
  obtain ⟨s0, hs0, hs'⟩ := hs'
  obtain ⟨t0, ht0, ht'⟩ := ht'
  have hs0borel : MeasurableSet s0 :=
    (lowerShellLocalSigma_le_borel m U) s0 hs0
  have ht0borel : MeasurableSet t0 :=
    (lowerShellLocalSigma_le_borel m V) t0 ht0
  have hsCut := ae_preimage_cutoffSampleLaw M hs'
  have htCut := ae_preimage_cutoffSampleLaw M ht'
  have hstCut : (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' (s' ∩ t') =ᵐ[
      (cutoffSampleLaw M).toMeasure]
      (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' (s0 ∩ t0) := by
    simpa only [Set.preimage_inter] using hsCut.inter htCut
  rw [← Set.preimage_inter]
  rw [measure_congr hstCut, measure_congr hsCut, measure_congr htCut,
    measure_preimage_cutoffSampleLaw M (hs0borel.inter ht0borel),
    measure_preimage_cutoffSampleLaw M hs0borel,
    measure_preimage_cutoffSampleLaw M ht0borel]
  exact (Indep_iff _ _ M.P.toMeasure).mp h s0 t0
    ⟨s0, hs0, Filter.EventuallyEq.rfl⟩ ⟨t0, ht0, Filter.EventuallyEq.rfl⟩

end

end Algsuperdiff.Section3.Cutoff

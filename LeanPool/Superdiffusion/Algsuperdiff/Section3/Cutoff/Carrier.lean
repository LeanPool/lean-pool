/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Summability
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Model
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Carrier

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The public lower-tail sample carrier

The genuine lower-infinite cutoff is defined only on the full-measure carrier
where every required lower shell tail converges.  This module supplies that
carrier and its canonical induced probability law; it deliberately does not
define a cutoff value.

## Main definitions

* `Algsuperdiff.Section3.Cutoff.CutoffSample`: the exact lower-tail-good
  subtype of the canonical shell-sequence carrier.
* `Algsuperdiff.Section3.Cutoff.cutoffSampleLaw`: the canonical shell law
  induced on that subtype.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The public sample carrier for the genuine lower-infinite cutoff.  Its
elements are exactly the shell sequences satisfying `LowerTailGood`. -/
abbrev CutoffSample (d : ℕ) :=
  {omega : ShellSeq d // LowerTailGood omega}

theorem ae_mem_range_cutoffSample_val (M : ABKModel d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      omega ∈ Set.range (Subtype.val : CutoffSample d → ShellSeq d) := by
  filter_upwards [ae_lowerTailGood M] with omega homega
  exact ⟨⟨omega, homega⟩, rfl⟩

/-- The canonical probability law restricted to the exact lower-tail-good
carrier. -/
noncomputable def cutoffSampleLaw (M : ABKModel d) :
    ProbabilityMeasure (CutoffSample d) :=
  ⟨Measure.comap (Subtype.val : CutoffSample d → ShellSeq d) M.P.toMeasure,
    (MeasurableEmbedding.subtype_coe (measurableSet_lowerTailGoodSet d)).isProbabilityMeasure_comap
      (by exact ae_mem_range_cutoffSample_val M)⟩

/-- Pushing the induced cutoff-sample law forward along `Subtype.val` recovers
the original canonical shell-sequence law. -/
theorem map_cutoffSampleLaw_val (M : ABKModel d) :
    Measure.map (Subtype.val : CutoffSample d → ShellSeq d)
        (cutoffSampleLaw M).toMeasure = M.P.toMeasure := by
  calc
    Measure.map (Subtype.val : CutoffSample d → ShellSeq d)
        (cutoffSampleLaw M).toMeasure =
        M.P.toMeasure.restrict {omega | LowerTailGood omega} := by
      exact map_comap_subtype_coe (measurableSet_lowerTailGoodSet d) M.P.toMeasure
    _ = M.P.toMeasure :=
      Measure.restrict_eq_self_of_ae_mem (ae_lowerTailGood M)

end

end Algsuperdiff.Section3.Cutoff

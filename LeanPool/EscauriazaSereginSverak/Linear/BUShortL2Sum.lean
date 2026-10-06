/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCarlemanData

/-!
# Quadratic sum of cutoff data

Global `L²` bounds imply finiteness of the four-term quadratic integral
required by the Sobolev half-space Carleman estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Four globally square-integrable weak data fields have finite summed
quadratic energy on any measurable subregion. -/
theorem bu_memLp_four_sum_lintegral_lt_top
    (S : Set ParabolicPoint)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hw : MemLp w 2 volume)
    (hDw : MemLp Dw 2 volume)
    (hD2w : MemLp D2w 2 volume)
    (hDtw : MemLp Dtw 2 volume) :
    (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
      ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hwS : MemLp w 2 (volume.restrict S) :=
    hw.mono_measure Measure.restrict_le_self
  have hDwS : MemLp Dw 2 (volume.restrict S) :=
    hDw.mono_measure Measure.restrict_le_self
  have hD2S : MemLp D2w 2 (volume.restrict S) :=
    hD2w.mono_measure Measure.restrict_le_self
  have hDtS : MemLp Dtw 2 (volume.restrict S) :=
    hDtw.mono_measure Measure.restrict_le_self
  have hfin (E : Type) [NormedAddCommGroup E]
      (f : ParabolicPoint → E) (hf : MemLp f 2 (volume.restrict S)) :
      (∫⁻ z in S, ‖f z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hf.aestronglyMeasurable).1 hf
    simpa using h
  have hA := hfin _ w hwS
  have hB := hfin _ Dw hDwS
  have hC := hfin _ D2w hD2S
  have hD := hfin _ Dtw hDtS
  have hmA : AEMeasurable (fun z => ‖w z‖ₑ ^ (2 : ℝ))
      (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hwS.aestronglyMeasurable.enorm
  have hmB : AEMeasurable (fun z => ‖Dw z‖ₑ ^ (2 : ℝ))
      (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hDwS.aestronglyMeasurable.enorm
  have hmC : AEMeasurable (fun z => ‖D2w z‖ₑ ^ (2 : ℝ))
      (volume.restrict S) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hD2S.aestronglyMeasurable.enorm
  have hAB : (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ)) := by
    simpa only [Pi.add_apply] using
      (lintegral_add_left' hmA (fun z => ‖Dw z‖ₑ ^ (2 : ℝ)))
  have hABC : (∫⁻ z in S,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in S, ‖D2w z‖ₑ ^ (2 : ℝ)) := by
    simpa only [Pi.add_apply] using
      (lintegral_add_left' (hmA.add hmB)
        (fun z => ‖D2w z‖ₑ ^ (2 : ℝ)))
  have hABCD : (∫⁻ z in S,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in S,
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
          ‖D2w z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in S, ‖Dtw z‖ₑ ^ (2 : ℝ)) := by
    simpa only [Pi.add_apply] using
      (lintegral_add_left' ((hmA.add hmB).add hmC)
        (fun z => ‖Dtw z‖ₑ ^ (2 : ℝ)))
  rw [hABCD, hABC, hAB]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hA, hB⟩, hC⟩, hD⟩

end ESS

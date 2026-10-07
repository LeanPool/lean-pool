/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCells

/-!
# Integration over shifted dyadic cells

Translation of the dyadic partition preserves parabolic measure.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The time translation carries a dyadic layer to its shifted
Carleman-time layer. -/
theorem bu_short_shifted_dyadic_layer_image (k : ℤ) :
    buGaussianTimeShiftPoint (1 / 2 : ℝ) ''
      (Set.univ ×ˢ Set.Ioo
        (Foundation.buSmallTimeDyadicScale k / 2)
        (Foundation.buSmallTimeDyadicScale k) : Set ParabolicPoint) =
      (Set.univ ×ˢ Set.Ioo
        (1 / 2 + Foundation.buSmallTimeDyadicScale k / 2)
        (1 / 2 + Foundation.buSmallTimeDyadicScale k) :
          Set ParabolicPoint) := by
  let T := buGaussianTimeShiftPoint (1 / 2 : ℝ)
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [bu_short_time_shift_point_eval]
    exact ⟨Set.mem_univ _,
      ⟨by linarith only [hq.2.1], by linarith only [hq.2.2]⟩⟩
  · intro hz
    let q : ParabolicPoint := T.symm z
    have hqcoord := buGaussian_timeShift_point_symm_apply (1 / 2 : ℝ) z
    have hq : q ∈ Set.univ ×ˢ Set.Ioo
        (Foundation.buSmallTimeDyadicScale k / 2)
        (Foundation.buSmallTimeDyadicScale k) := by
      refine ⟨Set.mem_univ _, ?_⟩
      change _ < q.2 ∧ q.2 < _
      have hqtime : q.2 = z.2 - 1 / 2 := by
        simpa only [q, T] using congrArg (fun p : ParabolicPoint => p.2) hqcoord
      rw [hqtime]
      constructor <;> linarith only [hz.2.1, hz.2.2]
    exact ⟨q, hq, T.apply_symm_apply z⟩

/-- Nonnegative integration over a shifted dyadic layer equals the
sum over its shifted cells (`lem:bu-small-time`). -/
theorem bu_short_shifted_dyadic_layer_lintegral_eq_tsum
    (k : ℤ) (f : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ z in (Set.univ ×ˢ Set.Ioo
        (1 / 2 + Foundation.buSmallTimeDyadicScale k / 2)
        (1 / 2 + Foundation.buSmallTimeDyadicScale k) :
          Set ParabolicPoint), f z ∂(volume : Measure ParabolicPoint)) =
      ∑' ij : (Fin 3 → ℤ) × Fin 2048,
        ∫⁻ z in buShortShiftedDyadicCell k ij.1 ij.2,
          f z ∂(volume : Measure ParabolicPoint) := by
  let T := buGaussianTimeShiftPoint (1 / 2 : ℝ)
  have htrans (S : Set ParabolicPoint) :
      (∫⁻ z in T '' S, f z ∂(volume : Measure ParabolicPoint)) =
        ∫⁻ q in S, f (T q) ∂(volume : Measure ParabolicPoint) := by
    exact (buGaussian_timeShift_measurePreserving (1 / 2 : ℝ)).setLIntegral_comp_emb
      T.measurableEmbedding f S |>.symm
  have hLayer := Foundation.buSmallTimeDyadicCell_lintegral_eq_tsum k
    (fun q => f (T q))
  calc
    _ = ∫⁻ z in T '' (Set.univ ×ˢ Set.Ioo
        (Foundation.buSmallTimeDyadicScale k / 2)
        (Foundation.buSmallTimeDyadicScale k) : Set ParabolicPoint),
          f z ∂(volume : Measure ParabolicPoint) := by rw [bu_short_shifted_dyadic_layer_image]
    _ = ∫⁻ q in (Set.univ ×ˢ Set.Ioo
        (Foundation.buSmallTimeDyadicScale k / 2)
        (Foundation.buSmallTimeDyadicScale k) : Set ParabolicPoint),
          f (T q) ∂(volume : Measure ParabolicPoint) := htrans _
    _ = ∑' ij : (Fin 3 → ℤ) × Fin 2048,
          ∫⁻ q in Foundation.buSmallTimeDyadicCell k ij.1 ij.2,
            f (T q) ∂(volume : Measure ParabolicPoint) := hLayer
    _ = ∑' ij : (Fin 3 → ℤ) × Fin 2048,
          ∫⁻ z in buShortShiftedDyadicCell k ij.1 ij.2,
            f z ∂(volume : Measure ParabolicPoint) := by
      apply tsum_congr
      intro ij
      exact (htrans (Foundation.buSmallTimeDyadicCell k ij.1 ij.2)).symm

end ESS

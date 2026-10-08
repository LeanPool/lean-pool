/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortDyadicLayerCover
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Almost-everywhere coverage by shifted cells

The shifted spatial and temporal grid covers each dyadic layer up to
null time boundaries.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A shifted dyadic cell is measurable. -/
theorem bu_short_shifted_dyadic_cell_measurable
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    MeasurableSet (buShortShiftedDyadicCell k m ell) := by
  have hOld : MeasurableSet
      (Foundation.buSmallTimeDyadicCell k m ell) := by
    exact (MeasurableSet.pi Set.countable_univ
      (fun i _ => measurableSet_Ico)).prod measurableSet_Ioo
  exact (buGaussianTimeShiftPoint (1 / 2 : ℝ)).measurableEmbedding.measurableSet_image.mpr
    hOld

/-- Each shifted cell lies in its shifted dyadic time layer. -/
theorem bu_short_shifted_dyadic_cell_subset_layer
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    buShortShiftedDyadicCell k m ell ⊆
      (Set.univ ×ˢ Ioo
        (1 / 2 + Foundation.buSmallTimeDyadicScale k / 2)
        (1 / 2 + Foundation.buSmallTimeDyadicScale k) :
          Set ParabolicPoint) := by
  rintro z ⟨q, hq, rfl⟩
  have hqLayer := Foundation.buSmallTimeDyadicCell_subset_layer k m ell hq
  rw [bu_short_time_shift_point_eval]
  exact ⟨Set.mem_univ _,
    ⟨by linarith only [hqLayer.2.1], by linarith only [hqLayer.2.2]⟩⟩

/-- Shifted cells cover their dyadic layer almost everywhere. -/
theorem bu_short_shifted_dyadic_cells_cover_ae (k : ℤ) :
    (⋃ ij : (Fin 3 → ℤ) × Fin 2048,
      buShortShiftedDyadicCell k ij.1 ij.2) =ᵐ[volume]
      (Set.univ ×ˢ Ioo
        (1 / 2 + Foundation.buSmallTimeDyadicScale k / 2)
        (1 / 2 + Foundation.buSmallTimeDyadicScale k) :
          Set ParabolicPoint) := by
  let C : Set ParabolicPoint := ⋃ ij : (Fin 3 → ℤ) × Fin 2048,
    buShortShiftedDyadicCell k ij.1 ij.2
  let L : Set ParabolicPoint := Set.univ ×ˢ Ioo
    (1 / 2 + Foundation.buSmallTimeDyadicScale k / 2)
    (1 / 2 + Foundation.buSmallTimeDyadicScale k)
  let S : Set ParabolicPoint := L \ C
  have hCmeas : MeasurableSet C := by
    exact MeasurableSet.iUnion (fun ij =>
      bu_short_shifted_dyadic_cell_measurable k ij.1 ij.2)
  have hLmeas : MeasurableSet L := MeasurableSet.univ.prod measurableSet_Ioo
  have hSmeas : MeasurableSet S := hLmeas.diff hCmeas
  have hCL : C ⊆ L := by
    intro z hz
    rcases mem_iUnion.mp hz with ⟨ij, hij⟩
    exact bu_short_shifted_dyadic_cell_subset_layer k ij.1 ij.2 hij
  have hSsub : S ⊆ L := sdiff_subset
  have hSCempty (ij : (Fin 3 → ℤ) × Fin 2048) :
      S ∩ buShortShiftedDyadicCell k ij.1 ij.2 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1.2 (mem_iUnion.mpr ⟨ij, hz.2⟩)
  have hcellzero (ij : (Fin 3 → ℤ) × Fin 2048) :
      (∫⁻ z in buShortShiftedDyadicCell k ij.1 ij.2,
        S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂volume) = 0 := by
    rw [setLIntegral_indicator hSmeas, hSCempty]
    simp
  have hpartition := bu_short_shifted_dyadic_layer_lintegral_eq_tsum k
    (S.indicator (fun _ => (1 : ℝ≥0∞)))
  have hSnull : volume S = 0 := by
    calc
      volume S = ∫⁻ z in S, (1 : ℝ≥0∞) ∂volume := by simp
      _ = ∫⁻ z in L, S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂volume := by
        rw [setLIntegral_indicator hSmeas, Set.inter_eq_left.mpr hSsub]
      _ = ∑' ij : (Fin 3 → ℤ) × Fin 2048,
            ∫⁻ z in buShortShiftedDyadicCell k ij.1 ij.2,
              S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂volume := hpartition
      _ = 0 := by simp only [hcellzero, tsum_zero]
  apply (ae_eq_set).2
  constructor
  · change volume (C \ L) = 0
    rw [Set.sdiff_eq_empty.mpr hCL]
    simp
  · exact hSnull

/-- All shifted dyadic cells cover the short normalized slab almost
everywhere (`lem:bu-small-time`). -/
theorem bu_short_shifted_all_cells_cover_ae :
    (⋃ ij : (ℕ × (Fin 3 → ℤ)) × Fin 2048,
      buShortShiftedDyadicCell (ij.1.1 + 1 : ℤ) ij.1.2 ij.2) =ᵐ[volume]
      (Set.univ ×ˢ Ioo (1 / 2 : ℝ) 1 : Set ParabolicPoint) := by
  have hreindex :
      (⋃ ij : (ℕ × (Fin 3 → ℤ)) × Fin 2048,
        buShortShiftedDyadicCell (ij.1.1 + 1 : ℤ) ij.1.2 ij.2) =
      ⋃ k : ℕ, ⋃ ij : (Fin 3 → ℤ) × Fin 2048,
        buShortShiftedDyadicCell (k + 1 : ℤ) ij.1 ij.2 := by
    ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨⟨⟨k, m⟩, ell⟩, hz⟩
      exact ⟨k, ⟨(m, ell), hz⟩⟩
    · rintro ⟨k, ⟨⟨m, ell⟩, hz⟩⟩
      exact ⟨((k, m), ell), hz⟩
  rw [hreindex]
  have hCells := Filter.EventuallyEqSet.countable_iUnion
    (fun k : ℕ => bu_short_shifted_dyadic_cells_cover_ae (k + 1 : ℤ))
  exact hCells.trans bu_short_shifted_parabolic_layers_ae

end ESS

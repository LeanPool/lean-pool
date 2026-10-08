/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AffineGridDistortion
public import LeanPool.HighContrastHomogenization.Entry.Geometry.SourceWhitneyDecomposition
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows

/-!
# High-contrast homogenization: Entry.Geometry.AffineWhitneyCounts

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Count-facing facts for adapted Whitney rows

Finite-level part (i) of `l.two.grid.whitney`: individual cell volume,
top-generation packing, and lower-generation volume and cardinality estimates.
The proof works in relative coordinates, using parent escape and flat-face strips.
`twoGridWhitneyCounts` chooses one constant before all grids, scales and translations;
it includes partition and finiteness, while the series identity and hybrid construction
remain outside this support module.
-/

open HCPolySupport.HighContrast (adaptedCellCenter gridRatio)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate standardCell)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

theorem adaptedCell_relVolume_le_of_gridRatio
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j r : ℤ) (y : Vec d) :
    (volume (adaptedCell q r)).toReal /
        (volume (adaptedCellTranslate q' j y)).toReal ≤
      ((Nat.factorial d : ℝ) * K₀ ^ d) *
        (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ))) :=
  (adaptedCell_volume_ratio_two_sided_of_gridRatio hd hK₀ hq hq' hK j r y).2

theorem topGenerationPacking_le_of_gridRatio [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j ℓ : ℤ) (hℓ : 1 ≤ ℓ) (y : Vec d) :
    let W : Set (Vec d) := adaptedCellTranslate q' j y
    let n : ℤ := j - ℓ
    ((finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (W := W) (by simpa [W] using Transport.volume_adaptedCellTranslate_ne_top q' j y) n
          n).toFinset.card : ℝ)
      ≤ ((Nat.factorial d : ℝ) * K₀ ^ d) * (3 : ℝ) ^ ((d : ℝ) * (ℓ : ℝ)) := by
  classical
  dsimp
  have _hℓ_nonneg : (0 : ℤ) ≤ ℓ := le_trans (by norm_num) hℓ
  let W : Set (Vec d) := adaptedCellTranslate q' j y
  let n : ℤ := j - ℓ
  let hfinI : (maximalAdaptedCellIndices W q n n).Finite :=
    finite_maximalAdaptedCellIndices_of_volume_ne_top hq
      (by simp [W, Transport.volume_adaptedCellTranslate_ne_top]) n n
  let S : Finset (Fin d → ℤ) := hfinI.toFinset
  have hSsub : ↑S ⊆ maximalAdaptedCellIndices W q n n := by
    intro w hw
    exact hfinI.mem_toFinset.mp (by simpa [S] using hw)
  have hsum_meas :
      ∑ w ∈ S, volume (adaptedCellAtCenter q n w) ≤ volume W := by
    have hdis :
        (S : Set (Fin d → ℤ)).PairwiseDisjoint fun w => adaptedCellAtCenter q n w :=
      (pairwiseDisjoint_maximalAdaptedCellIndices W q hq n n).subset hSsub
    have hmeas : ∀ w ∈ S, MeasurableSet (adaptedCellAtCenter q n w) := by
      intro w _
      unfold adaptedCellAtCenter
      exact (isOpen_adaptedCellTranslate hq n (adaptedCellCenter q n w)).measurableSet
    calc
      ∑ w ∈ S, volume (adaptedCellAtCenter q n w)
          = volume (⋃ w ∈ S, adaptedCellAtCenter q n w) := by
            rw [measure_biUnion_finset hdis hmeas]
      _ ≤ volume W := by
            refine measure_mono ?_
            rintro x hx
            obtain ⟨w, hwS, hxw⟩ := Set.mem_iUnion₂.mp hx
            exact IsMaximalAdaptedCellIn.subset (hSsub hwS) hxw
  have hW_ne_top : volume W ≠ ⊤ := by
    simpa [W] using Transport.volume_adaptedCellTranslate_ne_top q' j y
  have hsum_real := ENNReal.toReal_mono hW_ne_top hsum_meas
  have hcell_ne_top : ∀ w ∈ S, volume (adaptedCellAtCenter q n w) ≠ ⊤ := by
    intro w _
    exact volume_adaptedCellAtCenter_ne_top q n w
  rw [ENNReal.toReal_sum hcell_ne_top] at hsum_real
  have hsame :
      (∑ w ∈ S, (volume (adaptedCellAtCenter q n w)).toReal)
        = (S.card : ℝ) * (volume (adaptedCell q n)).toReal := by
    rw [Finset.sum_congr rfl fun w _ => by
      calc
        (volume (adaptedCellAtCenter q n w)).toReal =
            (ENNReal.ofReal |q.det| * ENNReal.ofReal ((3 : ℝ) ^ n) ^ d).toReal := by
          rw [volume_adaptedCellAtCenter]
        _ = (volume (adaptedCell q n)).toReal := by
          rw [volume_adaptedCell]]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcell_pos : 0 < (volume (adaptedCell q n)).toReal := by
    rw [volume_adaptedCell_toReal]
    have hdet : q.det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
    positivity
  have hW_pos : 0 < (volume W).toReal := by
    rw [show W = adaptedCellTranslate q' j y by rfl, volume_adaptedCellTranslate_toReal]
    have hdet : q'.det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q').mp hq')
    positivity
  have hcard_index_le :
      (S.card : ℝ) ≤ (volume W).toReal / (volume (adaptedCell q n)).toReal := by
    rw [hsame] at hsum_real
    exact (le_div_iff₀ hcell_pos).mpr hsum_real
  let Cdet : ℝ := (Nat.factorial d : ℝ) * K₀ ^ d
  let scale : ℝ := (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (n : ℝ)))
  have hCdet_pos : 0 < Cdet := by
    dsimp [Cdet]
    positivity
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hratio_lower :
      Cdet⁻¹ * scale ≤
        (volume (adaptedCell q n)).toReal / (volume W).toReal := by
    simpa [Cdet, scale, W] using
      (adaptedCell_volume_ratio_two_sided_of_gridRatio hd hK₀ hq hq' hK j n y).1
  have hratio_pos :
      0 < (volume (adaptedCell q n)).toReal / (volume W).toReal :=
    div_pos hcell_pos hW_pos
  have hdiv_eq_inv :
      (volume W).toReal / (volume (adaptedCell q n)).toReal =
        ((volume (adaptedCell q n)).toReal / (volume W).toReal)⁻¹ := by
    field_simp [ne_of_gt hcell_pos, ne_of_gt hW_pos]
  have hdiv_bound :
      (volume W).toReal / (volume (adaptedCell q n)).toReal ≤
        (Cdet⁻¹ * scale)⁻¹ := by
    rw [hdiv_eq_inv]
    exact (inv_le_inv₀ hratio_pos (mul_pos (inv_pos.mpr hCdet_pos) hscale_pos)).mpr
      hratio_lower
  have hscale_inv :
      (Cdet⁻¹ * scale)⁻¹ =
        Cdet * (3 : ℝ) ^ ((d : ℝ) * (ℓ : ℝ)) := by
    have hn_cast : (n : ℝ) = (j : ℝ) - (ℓ : ℝ) := by
      dsimp [n]
      norm_num
    have hjn : (j : ℝ) - (n : ℝ) = (ℓ : ℝ) := by
      rw [hn_cast]
      ring
    dsimp [scale]
    rw [hjn]
    rw [mul_inv_rev]
    rw [inv_inv]
    have hexp : (-(d : ℝ) * (ℓ : ℝ)) = -((d : ℝ) * (ℓ : ℝ)) := by ring
    rw [hexp]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) ((d : ℝ) * (ℓ : ℝ))]
    rw [inv_inv]
    ring
  have hcenter_card_le :
      ((finite_maximalAdaptedCellCenters_of_volume_ne_top hq
          (Transport.volume_adaptedCellTranslate_ne_top q' j y) n n).toFinset.card : ℝ)
        ≤ (S.card : ℝ) := by
    have hcent_fin :
        (maximalAdaptedCellCenters W q n n).Finite :=
      finite_maximalAdaptedCellCenters_of_volume_ne_top hq hW_ne_top n n
    have hncard :
        (maximalAdaptedCellCenters W q n n).ncard ≤
          (maximalAdaptedCellIndices W q n n).ncard := by
      rw [maximalAdaptedCellCenters_eq_image_indices]
      exact Set.ncard_image_le hfinI
    have hleft :
        (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
            (Transport.volume_adaptedCellTranslate_ne_top q' j y) n n).toFinset.card =
          (maximalAdaptedCellCenters W q n n).ncard := by
      have := (Set.ncard_eq_toFinset_card
        (maximalAdaptedCellCenters (adaptedCellTranslate q' j y) q n n)
        (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
          (Transport.volume_adaptedCellTranslate_ne_top q' j y) n n)).symm
      simpa [W] using this
    have hright : S.card = (maximalAdaptedCellIndices W q n n).ncard := by
      have := (Set.ncard_eq_toFinset_card (maximalAdaptedCellIndices W q n n) hfinI).symm
      simpa [S] using this
    exact_mod_cast (by
      rw [hleft, hright]
      exact hncard)
  exact hcenter_card_le.trans (hcard_index_le.trans (hdiv_bound.trans (by rw [hscale_inv])))

/-- Flat-face volume bound for a capped lower row in relative coordinates.
The cap is independent of the target generation; no openness of a complement is used. -/
theorem volume_lowerRow_preimage_le_of_gridRatio [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n r : ℤ) (hr : r < n) (y : Vec d) :
    let V := adaptedCellTranslate (q⁻¹ * q') j (matVecMul q⁻¹ y)
    volume (⋃ w ∈ maximalCellIndices V n r, standardCell d r w) ≤
      ENNReal.ofReal ((6 * (d : ℝ) * K₀ * Real.sqrt d) *
        (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) * volume V := by
  dsimp
  have hvol := volume_le_of_near_complement (le_trans zero_le_one hK₀)
    (inverseNormLE_relative_of_gridRatio hd hq hq' hK)
    (j := j) (y := matVecMul q⁻¹ y)
    (A := ⋃ w ∈ maximalCellIndices
      (adaptedCellTranslate (q⁻¹ * q') j (matVecMul q⁻¹ y)) n r, standardCell d r w)
    (s := Real.sqrt d * (3 : ℝ) ^ (r + 1)) (by positivity)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact hw.subset hxw)
    (by
      rintro x hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      exact exists_not_mem_of_mem_maximalCell hr hw hxw)
  have hc : 2 * (d : ℝ) * (K₀ * (Real.sqrt d * (3 : ℝ) ^ (r + 1))) *
      (3 : ℝ) ^ (-j) = (6 * (d : ℝ) * K₀ * Real.sqrt d) *
        (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
    rw [← Int.cast_sub, Real.rpow_intCast, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0),
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, div_eq_mul_inv]
    ring
  rwa [hc] at hvol

/-- The printed lower-row relative-volume estimate, for any cap `n` and `r < n`.
The constant depends only on dimension and relative distortion. -/
theorem lowerRowRelVolume_le_of_gridRatio [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n r : ℤ) (hr : r < n) (y : Vec d) :
    ∑ _z ∈ (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (Transport.volume_adaptedCellTranslate_ne_top q' j y) n r).toFinset,
      (volume (adaptedCell q r)).toReal / (volume (adaptedCellTranslate q' j y)).toReal ≤
        (6 * (d : ℝ) * K₀ * Real.sqrt d) * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
  classical
  have hInv := inverseNormLE_relative_of_gridRatio hd hq hq' hK
  have hsum := sum_relVolume_le_of_volume_le
    (volume_adaptedCellTranslate_pos hInv j (matVecMul q⁻¹ y)).ne'
    (Transport.volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y))
    (by positivity : 0 ≤ (6 * (d : ℝ) * K₀ * Real.sqrt d) *
      (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)))
    (volume_lowerRow_preimage_le_of_gridRatio hd hK₀ hq hq' hK j n r hr y)
  simp_rw [← adaptedCell_relVolume_eq_standard_preimage hq hq' j r y] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum ⊢
  have hcard :
      (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (Transport.volume_adaptedCellTranslate_ne_top q' j y) n r).toFinset.card =
      (finite_maximalCellIndices
        (Transport.volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y)) n
          r).toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _
        (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
          (Transport.volume_adaptedCellTranslate_ne_top q' j y) n r),
      ← Set.ncard_eq_toFinset_card _
        (finite_maximalCellIndices
          (Transport.volume_adaptedCellTranslate_ne_top (q⁻¹ * q') j (matVecMul q⁻¹ y)) n r),
      ncard_maximalAdaptedCellCenters_eq_preimage hq,
      preimage_matVecMul_adaptedCellTranslate_eq hq]
  rw [hcard]
  exact hsum

/-- Divide the lower-row volume bound by the positive lower cell-volume comparison. -/
theorem lowerRowCard_le_of_gridRatio [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n r : ℤ) (hr : r < n) (y : Vec d) :
    ((finite_maximalAdaptedCellCenters_of_volume_ne_top hq
        (Transport.volume_adaptedCellTranslate_ne_top q' j y) n r).toFinset.card : ℝ) ≤
      ((6 * (d : ℝ) * K₀ * Real.sqrt d) * ((Nat.factorial d : ℝ) * K₀ ^ d)) *
        (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (r : ℝ))) := by
  classical
  let D : ℝ := (Nat.factorial d : ℝ) * K₀ ^ d
  let A : ℝ := 6 * (d : ℝ) * K₀ * Real.sqrt d
  have hD : 0 < D := by dsimp [D]; positivity
  have hf : 0 < D⁻¹ * (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ))) := by positivity
  have hrow := lowerRowRelVolume_le_of_gridRatio hd hK₀ hq hq' hK j n r hr y
  simp only [Finset.sum_const, nsmul_eq_mul] at hrow
  have hlo := (adaptedCell_volume_ratio_two_sided_of_gridRatio hd hK₀ hq hq' hK j r y).1
  have h := (mul_le_mul_of_nonneg_left hlo
    (Nat.cast_nonneg (finite_maximalAdaptedCellCenters_of_volume_ne_top hq
      (Transport.volume_adaptedCellTranslate_ne_top q' j y) n r).toFinset.card)).trans hrow
  have heq : ((A * D) * (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (r : ℝ)))) *
      (D⁻¹ * (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ)))) =
        A * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
    calc
      _ = A * (D * D⁻¹) * ((3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (r : ℝ))) *
          (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ)))) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ hD.ne', mul_one, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 2
        ring
  change _ ≤ (A * D) * (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (r : ℝ)))
  apply (mul_le_mul_iff_left₀ hf).mp
  rw [heq]
  exact h

/-- Finite-level part (i) of `l.two.grid.whitney`.
One constant is chosen before all grids, scales and translations. Null exhaustion
is included; the infinite-series identity and the hybrid construction are separate tasks. -/
theorem twoGridWhitneyCounts (d : ℕ) (hd : 2 ≤ d) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q q' : Mat d), IsUnit q → IsUnit q' →
      gridRatio q q' ≤ K₀ → ∀ (j ℓ : ℤ), 1 ≤ ℓ → ∀ y : Vec d,
      let W := adaptedCellTranslate q' j y
      ∃ hfin : ∀ r : ℤ, r ≤ j - ℓ → (maximalAdaptedCellCenters W q (j - ℓ) r).Finite,
        (∀ (r : ℤ) (w : Fin d → ℤ), IsMaximalAdaptedCellIn W q (j - ℓ) r w →
          adaptedCellAtCenter q r w ⊆ W) ∧
        ({p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q (j - ℓ) p.1 p.2}).PairwiseDisjoint
          (fun p => adaptedCellAtCenter q p.1 p.2) ∧
        volume (W \
          ⋃ p ∈ {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q (j - ℓ) p.1 p.2},
            adaptedCellAtCenter q p.1 p.2) = 0 ∧
        (∀ r : ℤ, r ≤ j - ℓ →
          (volume (adaptedCell q r)).toReal / (volume W).toReal ≤
            C * (3 : ℝ) ^ (-(d : ℝ) * ((j : ℝ) - (r : ℝ)))) ∧
        ((hfin (j - ℓ) le_rfl).toFinset.card : ℝ) ≤ C * (3 : ℝ) ^ ((d : ℝ) * (ℓ : ℝ)) ∧
        (∀ (r : ℤ) (hr : r < j - ℓ), ((hfin r hr.le).toFinset.card : ℝ) ≤
          C * (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (r : ℝ)))) ∧
        (∀ (r : ℤ) (hr : r < j - ℓ),
          ∑ _z ∈ (hfin r hr.le).toFinset,
            (volume (adaptedCell q r)).toReal / (volume W).toReal ≤
              C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) := by
  let : NeZero d := ⟨by omega⟩
  let D : ℝ := (Nat.factorial d : ℝ) * K₀ ^ d
  let A : ℝ := 6 * (d : ℝ) * K₀ * Real.sqrt d
  let C : ℝ := D + A + A * D + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAD : 0 ≤ A * D := mul_nonneg hA hD.le
  have hDC : D ≤ C := by dsimp [C]; linarith only [hA, hAD]
  have hAC : A ≤ C := by dsimp [C]; linarith only [hD, hAD]
  have hADC : A * D ≤ C := by dsimp [C]; linarith only [hD, hA]
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q q' hq hq' hK j ℓ hℓ y W
  let hfin : ∀ r : ℤ, r ≤ j - ℓ → (maximalAdaptedCellCenters W q (j - ℓ) r).Finite :=
    fun r _ => finite_maximalAdaptedCellCenters_of_volume_ne_top hq
      (Transport.volume_adaptedCellTranslate_ne_top q' j y) (j - ℓ) r
  refine ⟨hfin, fun _ _ h => IsMaximalAdaptedCellIn.subset h,
    pairwiseDisjoint_maximalAdaptedCellPairs W q hq (j - ℓ),
    volume_diff_iUnion_maximalAdaptedCells_of_isOpen hq
      (isOpen_adaptedCellTranslate hq' j y) (j - ℓ), ?_, ?_, ?_, ?_⟩
  · intro r _
    exact (adaptedCell_relVolume_le_of_gridRatio hd hK₀ hq hq' hK j r y).trans
      (mul_le_mul_of_nonneg_right hDC (by positivity))
  · exact (topGenerationPacking_le_of_gridRatio hd hK₀ hq hq' hK j ℓ hℓ y).trans
      (mul_le_mul_of_nonneg_right hDC (by positivity))
  · intro r hr
    exact (lowerRowCard_le_of_gridRatio hd hK₀ hq hq' hK j (j - ℓ) r hr y).trans
      (mul_le_mul_of_nonneg_right hADC (by positivity))
  · intro r hr
    exact (lowerRowRelVolume_le_of_gridRatio hd hK₀ hq hq' hK j (j - ℓ) r hr y).trans
      (mul_le_mul_of_nonneg_right hAC (by positivity))

end HCPolySupport.HighContrast.Geometry

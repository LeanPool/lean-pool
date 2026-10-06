/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AffineWhitneyCounts
public import LeanPool.HighContrastHomogenization.Entry.Geometry.HybridWhitneyUncovered

/-!
# High-contrast homogenization: Entry.Geometry.TwoGridWhitney

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Countable volume assembly for the actual adapted Whitney rows

The rows are indexed by the entire admissible integer subtype and their
finite center sets. Summability is proved from finite measure before the
real series is evaluated, as required by `l.two.grid.whitney`.
-/

open HCPolySupport.HighContrast (adaptedCellCenter gridRatio)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate standardCell)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

/-- Center injectivity converts a disjoint index-row volume to the finite
center sum, for any witness of its finiteness. -/
theorem volume_maximalAdaptedCell_row_toReal [NeZero d]
    {q : Mat d} (hq : IsUnit q) (W : Set (Vec d)) (n r : ℤ)
    (hfin : (maximalAdaptedCellCenters W q n r).Finite) :
    (volume (⋃ w ∈ maximalAdaptedCellIndices W q n r, adaptedCellAtCenter q r w)).toReal =
      ∑ _z ∈ hfin.toFinset, (volume (adaptedCell q r)).toReal := by
  classical
  let hI : (maximalAdaptedCellIndices W q n r).Finite :=
    hfin.of_finite_image (adaptedCellCenter_injective q r hq).injOn
  have hcard : hfin.toFinset.card = hI.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, ← Set.ncard_eq_toFinset_card _ hI,
      maximalAdaptedCellCenters_eq_image_indices,
      Set.ncard_image_of_injective _ (adaptedCellCenter_injective q r hq)]
  have hvol : volume (⋃ w ∈ maximalAdaptedCellIndices W q n r, adaptedCellAtCenter q r w) =
      ∑ w ∈ hI.toFinset, volume (adaptedCellAtCenter q r w) := by
    have hdis : (hI.toFinset : Set (Fin d → ℤ)).PairwiseDisjoint
        (fun w => adaptedCellAtCenter q r w) := by
      rw [hI.coe_toFinset]
      exact pairwiseDisjoint_maximalAdaptedCellIndices W q hq n r
    have h := measure_biUnion_finset (μ := volume) hdis (fun w _ =>
      (isOpen_adaptedCellTranslate hq r (adaptedCellCenter q r w)).measurableSet)
    simpa only [hI.mem_toFinset] using h
  rw [hvol, ENNReal.toReal_sum (fun w _ => volume_adaptedCellAtCenter_ne_top q r w)]
  simp_rw [volume_adaptedCellAtCenter, ← volume_adaptedCell]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]

/-- The full admissible integer family is summable, with sum equal to the
measure of its actual pair-indexed union. Finite measure is used before
passing from the extended nonnegative series to a real series. -/
theorem hasSum_maximalAdaptedCell_row_volumes [NeZero d]
    {q : Mat d} (hq : IsUnit q) {W : Set (Vec d)} (hW : volume W ≠ ⊤) (n : ℤ)
    (hfin : ∀ r : ℤ, r ≤ n → (maximalAdaptedCellCenters W q n r).Finite) :
    HasSum (fun r : {r : ℤ // r ≤ n} =>
      ∑ _z ∈ (hfin r.1 r.2).toFinset, (volume (adaptedCell q r.1)).toReal)
      (volume (⋃ p ∈ {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q n p.1 p.2},
        adaptedCellAtCenter q p.1 p.2)).toReal := by
  let B (r : {r : ℤ // r ≤ n}) :=
    ⋃ w ∈ maximalAdaptedCellIndices W q n r.1, adaptedCellAtCenter q r.1 w
  have hBsub (r : {r : ℤ // r ≤ n}) : B r ⊆ W := by
    rintro x hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    exact hw.1.2 hxw
  have hBmeas (r : {r : ℤ // r ≤ n}) : MeasurableSet (B r) :=
    (isOpen_iUnion fun w => isOpen_iUnion fun _ =>
      isOpen_adaptedCellTranslate hq r.1 (adaptedCellCenter q r.1 w)).measurableSet
  have hBdis : Pairwise (fun r s => Disjoint (B r) (B s)) := by
    intro r s hrs
    refine Set.disjoint_left.mpr ?_
    intro x hxr hxs
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxr
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hxs
    have hpne : (r.1, w) ≠ (s.1, v) := by
      intro h
      exact hrs (Subtype.ext (congrArg Prod.fst h))
    exact Set.disjoint_left.mp (IsMaximalAdaptedCellIn.disjoint hq hw hv hpne) hxw hxv
  have hUnion : (⋃ r, B r) =
      ⋃ p ∈ {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q n p.1 p.2},
        adaptedCellAtCenter q p.1 p.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxr
      exact Set.mem_iUnion₂.mpr ⟨(r.1, w), hw, hxw⟩
    · intro hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion.mpr ⟨⟨p.1, hp.1.1⟩,
        Set.mem_iUnion₂.mpr ⟨p.2, hp, hxp⟩⟩
  have hvolume := measure_iUnion (μ := volume) hBdis hBmeas
  have hne : (∑' r, volume (B r)) ≠ ⊤ := by
    rw [← hvolume]
    exact ne_top_of_le_ne_top hW (measure_mono (Set.iUnion_subset hBsub))
  have hsum := (ENNReal.summable_toReal hne).hasSum
  rw [← ENNReal.tsum_toReal_eq (fun r =>
    ne_top_of_le_ne_top hW (measure_mono (hBsub r))), ← hvolume, hUnion] at hsum
  have hrow (r : {r : ℤ // r ≤ n}) : (volume (B r)).toReal =
      ∑ _z ∈ (hfin r.1 r.2).toFinset, (volume (adaptedCell q r.1)).toReal :=
    volume_maximalAdaptedCell_row_toReal hq W n r.1 (hfin r.1 r.2)
  simp_rw [hrow] at hsum
  exact hsum

/-- Every finite-volume open target of positive volume has total normalized
Whitney mass one, with genuine summability on the infinite lower half-line. -/
theorem hasSum_maximalAdaptedCell_relVolumes [NeZero d]
    {q : Mat d} (hq : IsUnit q) {W : Set (Vec d)} (hWopen : IsOpen W)
    (hW0 : volume W ≠ 0) (hW : volume W ≠ ⊤) (n : ℤ)
    (hfin : ∀ r : ℤ, r ≤ n → (maximalAdaptedCellCenters W q n r).Finite) :
    HasSum (fun r : {r : ℤ // r ≤ n} =>
      ∑ _z ∈ (hfin r.1 r.2).toFinset,
        (volume (adaptedCell q r.1)).toReal / (volume W).toReal) 1 := by
  have hmass := (hasSum_maximalAdaptedCell_row_volumes hq hW n hfin).div_const
    (volume W).toReal
  have hUnion : volume (⋃ p ∈ {p : ℤ × (Fin d → ℤ) |
      IsMaximalAdaptedCellIn W q n p.1 p.2}, adaptedCellAtCenter q p.1 p.2) = volume W := by
    refine measure_eq_measure_of_null_sdiff ?_
      (volume_diff_iUnion_maximalAdaptedCells_of_isOpen hq hWopen n)
    rintro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    exact hp.1.2 hxp
  rw [hUnion, div_self (ENNReal.toReal_ne_zero.mpr ⟨hW0, hW⟩)] at hmass
  simpa only [Finset.sum_div] using hmass

/-- A measure bound for an actual adapted row gives the normalized
center sum, with a separately specified positive finite denominator. -/
theorem maximalAdaptedCell_row_relVolume_le [NeZero d]
    {q : Mat d} (hq : IsUnit q) (W : Set (Vec d)) (n r : ℤ)
    (hfin : (maximalAdaptedCellCenters W q n r).Finite)
    {V : Set (Vec d)} (hV0 : volume V ≠ 0) (hV : volume V ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C)
    (hle : volume (⋃ w ∈ maximalAdaptedCellIndices W q n r, adaptedCellAtCenter q r w) ≤
      ENNReal.ofReal C * volume V) :
    ∑ _z ∈ hfin.toFinset, (volume (adaptedCell q r)).toReal / (volume V).toReal ≤ C := by
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hle
  rw [volume_maximalAdaptedCell_row_toReal hq W n r hfin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hreal
  rw [← Finset.sum_div, div_le_iff₀ (ENNReal.toReal_pos hV0 hV)]
  exact hreal

/-- Complete construction (i), including the infinite real-series identity.
The same positive constant is chosen before every grid, scale and translation. -/
theorem two_grid_whitney_part_one (d : ℕ) (hd : 2 ≤ d) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
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
        (∑' r : {r : ℤ // r ≤ j - ℓ},
          ∑ _z ∈ (hfin r.1 r.2).toFinset,
            (volume (adaptedCell q r.1)).toReal / (volume W).toReal) = 1 ∧
        (∀ (r : ℤ) (hr : r < j - ℓ),
          ∑ _z ∈ (hfin r hr.le).toFinset,
            (volume (adaptedCell q r)).toReal / (volume W).toReal ≤
              C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hcounts⟩ := twoGridWhitneyCounts d hd K₀ hK₀
  refine ⟨C, hC, ?_⟩
  intro q q' hq hq' hK j ℓ hℓ y W
  obtain ⟨hfin, hsub, hdis, hnull, hvol, hcap, hcount, hrow⟩ :=
    hcounts q q' hq hq' hK j ℓ hℓ y
  refine ⟨hfin, hsub, hdis, hnull, hvol, hcap, hcount, ?_, hrow⟩
  have hWpos : 0 < (volume W).toReal := by
    change 0 < (volume (adaptedCellTranslate q' j y)).toReal
    rw [volume_adaptedCellTranslate_toReal]
    have hdet : q'.det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q').mp hq')
    positivity
  exact (hasSum_maximalAdaptedCell_relVolumes hq (isOpen_adaptedCellTranslate hq' j y)
    (ENNReal.toReal_pos_iff.mp hWpos).1.ne'
    (Transport.volume_adaptedCellTranslate_ne_top q' j y) (j - ℓ) hfin).tsum_eq

/-- The hybrid construction's finiteness, exact null partition, and cap-row
estimate. The smaller-row exposed-face estimate is a separate obligation. -/
theorem hybrid_whitney_partition_cap [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n : ℤ) (y : Vec d) :
    let W := adaptedCellTranslate q j y
    let U := adaptedUncoveredPart W q' n
    ∃ hfin : ∀ r : ℤ, r ≤ n → (maximalAdaptedCellCenters U q n r).Finite,
      (∀ (r : ℤ) (w : Fin d → ℤ), IsMaximalAdaptedCellIn U q n r w →
        adaptedCellAtCenter q r w ⊆ U) ∧
      Set.PairwiseDisjoint
        {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn U q n p.1 p.2}
        (fun p => adaptedCellAtCenter q p.1 p.2) ∧
      volume (W \ (adaptedCoveredPart W q' n ∪
        ⋃ p ∈ {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn U q n p.1 p.2},
          adaptedCellAtCenter q p.1 p.2)) = 0 ∧
      (∑ _z ∈ (hfin n le_rfl).toFinset,
        (volume (adaptedCell q n)).toReal / (volume W).toReal) ≤
          (2 * (d : ℝ) * K₀ * Real.sqrt d) * (3 : ℝ) ^ ((n : ℝ) - (j : ℝ)) := by
  intro W U
  have hW : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q j y
  have hU : volume U ≠ ⊤ := ne_top_of_le_ne_top hW (measure_mono Set.sdiff_subset)
  let hfin : ∀ r : ℤ, r ≤ n → (maximalAdaptedCellCenters U q n r).Finite :=
    fun r _ => finite_maximalAdaptedCellCenters_of_volume_ne_top hq hU n r
  refine ⟨hfin, fun _ _ h => h.1.2, pairwiseDisjoint_maximalAdaptedCellPairs U q hq n,
    volume_diff_adaptedCoveredPart_union_maximalCells hq hq'
      (isOpen_adaptedCellTranslate hq j y) n, ?_⟩
  have hWpos : 0 < (volume W).toReal := by
    change 0 < (volume (adaptedCellTranslate q j y)).toReal
    rw [volume_adaptedCellTranslate_toReal]
    have hdet : q.det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
    positivity
  apply maximalAdaptedCell_row_relVolume_le hq U n n (hfin n le_rfl)
    (ENNReal.toReal_pos_iff.mp hWpos).1.ne' hW (by positivity)
  refine (measure_mono ?_).trans
    (volume_adaptedUncoveredPart_le_of_gridRatio hd hK₀ hq hq' hK j n y)
  rintro x hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  exact hw.1.2 hxw

/-- Every smaller selected old cube lies, away from the specified null
new-grid faces, near the outer boundary or an exposed packed face.
Both relative matrices are retained throughout the coordinate transport. -/
theorem hybrid_lower_row_subset_boundary_neighborhoods {d : ℕ} [NeZero d]
    {q q' : Mat d} {K₀ : ℝ} (hd : 2 ≤ d) (hK₀ : 1 ≤ K₀)
    (hq : IsUnit q) (hq' : IsUnit q') (hK : gridRatio q q' ≤ K₀)
    (j n r : ℤ) (hr : r < n) (y : Vec d) :
    let W := adaptedCellTranslate q j y
    let U := adaptedUncoveredPart W q' n
    let P := q⁻¹ * q'
    let c := 3 * (d : ℝ) * K₀ * Real.sqrt d
    let t := c * (3 : ℝ) ^ r
    let E := {w : Fin d → ℤ | adaptedCellAtCenter q' n w ⊆ W ∧
      ∃ (i : Fin d) (b : Bool), ¬ adaptedCellAtCenter q' n
        (Function.update w i (w i + if b then 1 else -1)) ⊆ W}
    let B (w : Fin d → ℤ) (i : Fin d) (b : Bool) :=
      let a : ℝ := ((w i : ℝ) + if b then 1 / 2 else -1 / 2) * (3 : ℝ) ^ n
      Set.pi Set.univ (Function.update
        (fun k : Fin d => Set.Icc (((w k : ℝ) - 1 / 2) * (3 : ℝ) ^ n - t)
          (((w k : ℝ) + 1 / 2) * (3 : ℝ) ^ n + t)) i (Set.Icc (a - t) (a + t)))
    ((⋃ w ∈ maximalAdaptedCellIndices U q n r, standardCell d r w) \
      matVecMul P '' gridFaces d n) ⊆
      ((fun v => matVecMul q⁻¹ y + matVecMul (1 : Mat d) v) ''
        boundaryStrips d j (Real.sqrt d * (3 : ℝ) ^ (r + 1))) ∪
      ⋃ w ∈ E, ⋃ i : Fin d, ⋃ b : Bool, matVecMul P '' B w i b := by
  intro W U P c t E B
  let M := q'⁻¹ * q
  let V := (matVecMul q') ⁻¹' W
  have hdet := (Matrix.isUnit_iff_isUnit_det q).mp hq
  have hdet' := (Matrix.isUnit_iff_isUnit_det q').mp hq'
  have hPM : P * M = 1 := by
    dsimp [P, M]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc q' q'⁻¹ q,
      Matrix.mul_nonsing_inv q' hdet', Matrix.one_mul, Matrix.nonsing_inv_mul q hdet]
  have hqM (x : Vec d) : matVecMul q' (matVecMul M x) = matVecMul q x := by
    rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec, Matrix.mulVec_mulVec]
    change Matrix.mulVec (q' * (q'⁻¹ * q)) x = Matrix.mulVec q x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv q' hdet', Matrix.one_mul]
  have hPMx (x : Vec d) : matVecMul P (matVecMul M x) = x := by
    rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec, Matrix.mulVec_mulVec, hPM, Matrix.one_mulVec]
  have hpreW : (matVecMul q) ⁻¹' W =
      adaptedCellTranslate (1 : Mat d) j (matVecMul q⁻¹ y) := by
    rw [preimage_matVecMul_adaptedCellTranslate_eq hq, Matrix.nonsing_inv_mul q hdet]
  have hCov (x : Vec d) : matVecMul M x ∈ adaptedCoveredPart V (1 : Mat d) n ↔
      matVecMul q x ∈ adaptedCoveredPart W q' n := by
    rw [← preimage_adaptedCoveredPart_self hq' W n, Set.mem_preimage, hqM]
  have hc1 (w : Fin d → ℤ) : adaptedCellAtCenter (1 : Mat d) n w = standardCell d n w := by
    have hid : matVecMul (1 : Mat d) = (fun v => v) :=
      funext fun v => by rw [matVecMul_eq_mulVec, Matrix.one_mulVec]
    rw [adaptedCellAtCenter_eq_affine_standardCell, hid]
    exact Set.image_id' _
  have hV : volume V ≠ ⊤ := volume_preimage_matVecMul_ne_top hq'
    (Transport.volume_adaptedCellTranslate_ne_top q j y)
  rintro x ⟨hxR, hxN⟩
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxR
  have hxU : matVecMul q x ∈ U := by
    apply hw.1.2
    rw [adaptedCellAtCenter_eq_affine_standardCell]
    exact ⟨x, hxw, rfl⟩
  obtain ⟨x', hx', hdist⟩ := exists_not_mem_preimage_of_mem_maximalAdaptedCell hq hr hw hxw
  by_cases hout : matVecMul q x' ∉ W
  · left
    have hInv : InverseNormLE (1 : Mat d) 1 := by
      intro v
      simp only [matVecMul_eq_mulVec, Matrix.one_mulVec, one_pow, one_mul, le_refl]
    have hxin : x ∈ adaptedCellTranslate (1 : Mat d) j (matVecMul q⁻¹ y) := by
      rw [← hpreW]
      exact hxU.1
    have hxout : x' ∉ adaptedCellTranslate (1 : Mat d) j (matVecMul q⁻¹ y) := by
      rwa [← hpreW]
    simpa only [one_mul] using mem_image_boundaryStrips zero_le_one hInv
      (by positivity : 0 ≤ Real.sqrt d * (3 : ℝ) ^ (r + 1)) hxin hxout hdist
  · right
    have hx'cov : matVecMul q x' ∈ adaptedCoveredPart W q' n := by
      by_contra h
      exact hx' ⟨not_not.mp hout, h⟩
    have hMxN : matVecMul M x ∉ gridFaces d n := fun h => hxN ⟨matVecMul M x, h, hPMx x⟩
    have hMx : matVecMul M x ∉ adaptedCoveredPart V (1 : Mat d) n :=
      fun h => hxU.2 ((hCov x).mp h)
    have hMx' : matVecMul M x' ∈ adaptedCoveredPart V (1 : Mat d) n := (hCov x').mpr hx'cov
    have hnear (i : Fin d) : |matVecMul M x i - matVecMul M x' i| ≤
        K₀ * (Real.sqrt d * (3 : ℝ) ^ (r + 1)) := by
      have hsum : vecNormSq (x - x') ≤ (Real.sqrt d * (3 : ℝ) ^ (r + 1)) ^ 2 := by
        simpa only [vecNormSq_eq_sum_sq, Pi.sub_apply] using hdist
      have hvec := (vecNormSq_relative_comm_le_gridRatio hd hK (x - x')).trans
        (mul_le_mul_of_nonneg_left hsum (sq_nonneg K₀))
      have hsq := (sq_apply_le_vecNormSq (matVecMul M (x - x')) i).trans hvec
      have heq : matVecMul M (x - x') i = matVecMul M x i - matVecMul M x' i := by
        rw [matVecMul_eq_mulVec, Matrix.mulVec_sub]
        rfl
      rw [heq, ← mul_pow] at hsq
      exact abs_le_of_sq_le_sq hsq (by positivity)
    obtain ⟨v, hv, i, b, hnot, hxbox⟩ := exposed_face_near_uncovered_point V hV n
      (matVecMul M x) (matVecMul M x') hMxN hMx hMx'
      (K₀ * (Real.sqrt d * (3 : ℝ) ^ (r + 1))) (by positivity) hnear
    have hvW : adaptedCellAtCenter q' n v ⊆ W :=
      (standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q' n v).mp ((hc1 v) ▸ hv)
    have hnotW : ¬ adaptedCellAtCenter q' n
        (Function.update v i (v i + if b then 1 else -1)) ⊆ W := by
      intro h
      apply hnot
      rw [hc1]
      exact (standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q' n _).mpr h
    have hwidth : (d : ℝ) * (K₀ * (Real.sqrt d * (3 : ℝ) ^ (r + 1))) = t := by
      dsimp [t, c]
      rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    refine Set.mem_iUnion₂.mpr ⟨v, ⟨hvW, i, b, hnotW⟩,
      Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨b, ?_⟩⟩⟩
    refine ⟨matVecMul M x, ?_, hPMx x⟩
    simpa only [hwidth] using hxbox

/-- The smaller hybrid row has width times surface-volume mass in old-grid
coordinates. The constant is chosen before both matrices and all scales. -/
theorem volume_hybrid_lower_row_le (d : ℕ) (hd : 2 ≤ d) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q q' : Mat d), IsUnit q → IsUnit q' →
      gridRatio q q' ≤ K₀ → ∀ (j n r : ℤ), r < n → ∀ y : Vec d,
      volume (⋃ w ∈ maximalAdaptedCellIndices
        (adaptedUncoveredPart (adaptedCellTranslate q j y) q' n) q n r,
        standardCell d r w) ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ r * ((3 : ℝ) ^ j) ^ (d - 1)) := by
  let : NeZero d := ⟨by omega⟩
  let D : ℝ := (Nat.factorial d : ℝ) * K₀ ^ d
  let c : ℝ := 3 * (d : ℝ) * K₀ * Real.sqrt d
  let A : ℝ := 6 * (d : ℝ) * Real.sqrt d
  let Ccube : ℝ := (4 * (d : ℝ) * K₀ * Real.sqrt d) * D
  let Cface : ℝ := Ccube * (2 * d) * D * (2 * c * (1 + 2 * c) ^ (d - 1))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCface : 0 ≤ Cface := by dsimp [Cface, Ccube, D]; positivity
  refine ⟨A + Cface + 1, by positivity, ?_⟩
  intro q q' hq hq' hK j n r hr y
  let W := adaptedCellTranslate q j y
  let U := adaptedUncoveredPart W q' n
  let P := q⁻¹ * q'
  let R := ⋃ w ∈ maximalAdaptedCellIndices U q n r, standardCell d r w
  let N := matVecMul P '' gridFaces d n
  let t := c * (3 : ℝ) ^ r
  let E := {w : Fin d → ℤ | adaptedCellAtCenter q' n w ⊆ W ∧
    ∃ (i : Fin d) (b : Bool), ¬ adaptedCellAtCenter q' n
      (Function.update w i (w i + if b then 1 else -1)) ⊆ W}
  let B (w : Fin d → ℤ) (i : Fin d) (b : Bool) :=
    let a : ℝ := ((w i : ℝ) + if b then 1 / 2 else -1 / 2) * (3 : ℝ) ^ n
    Set.pi Set.univ (Function.update
      (fun k : Fin d => Set.Icc (((w k : ℝ) - 1 / 2) * (3 : ℝ) ^ n - t)
        (((w k : ℝ) + 1 / 2) * (3 : ℝ) ^ n + t)) i (Set.Icc (a - t) (a + t)))
  let O := (fun v => matVecMul q⁻¹ y + matVecMul (1 : Mat d) v) ''
    boundaryStrips d j (Real.sqrt d * (3 : ℝ) ^ (r + 1))
  let S := (3 : ℝ) ^ r * ((3 : ℝ) ^ j) ^ (d - 1)
  have hcover : R \ N ⊆ O ∪ ⋃ w ∈ E, ⋃ i : Fin d, ⋃ b : Bool, matVecMul P '' B w i b :=
    hybrid_lower_row_subset_boundary_neighborhoods hd hK₀ hq hq' hK j n r hr y
  have hN : volume N = 0 := by
    have h := Transport.volume_image_affine P (0 : Vec d) (gridFaces d n)
    simp only [zero_add, volume_gridFaces, mul_zero] at h
    exact h
  have hE : E.Finite := (finite_contained_adaptedCellIndices hq'
    (Transport.volume_adaptedCellTranslate_ne_top q j y) n).subset (fun _ h => h.1)
  have hcount : (E.ncard : ℝ) ≤ Ccube *
      (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (n : ℝ))) :=
    ncard_exposed_adaptedCells_le_of_gridRatio hd hK₀ hq hq' hK j n y
  have hdet : |P.det| ≤ D := abs_det_inv_mul_le_gridRatio_of_le hd hK
  have hscale : (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (n : ℝ))) *
      ((3 : ℝ) ^ n) ^ (d - 1) = ((3 : ℝ) ^ j) ^ (d - 1) := by
    have hdn : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [← Real.rpow_intCast (3 : ℝ) n, ← Real.rpow_intCast (3 : ℝ) j,
      ← Real.rpow_natCast ((3 : ℝ) ^ (n : ℝ)) (d - 1),
      ← Real.rpow_natCast ((3 : ℝ) ^ (j : ℝ)) (d - 1),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hdn,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hfaces : volume (⋃ w ∈ E, ⋃ i : Fin d, ⋃ b : Bool, matVecMul P '' B w i b) ≤
      ENNReal.ofReal (Cface * S) := by
    have h := volume_iUnion_affine_face_neighborhoods_le P hE.toFinset n r hr.le hc
    simp only [hE.mem_toFinset, ← Set.ncard_eq_toFinset_card E hE] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      (E.ncard : ℝ) * (2 * d) * |P.det| *
          (2 * c * (1 + 2 * c) ^ (d - 1)) * (3 : ℝ) ^ r * ((3 : ℝ) ^ n) ^ (d - 1) ≤
        (Ccube * (3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (n : ℝ)))) * (2 * d) * D *
          (2 * c * (1 + 2 * c) ^ (d - 1)) * (3 : ℝ) ^ r * ((3 : ℝ) ^ n) ^ (d - 1) := by
        gcongr
      _ = Cface * S := by
        calc
          _ = Cface * (3 : ℝ) ^ r *
            ((3 : ℝ) ^ (((d : ℝ) - 1) * ((j : ℝ) - (n : ℝ))) *
              ((3 : ℝ) ^ n) ^ (d - 1)) := by dsimp [Cface]; ring
          _ = _ := by rw [hscale, mul_assoc]
  have houter : volume O ≤ ENNReal.ofReal (A * S) := by
    calc
      volume O = volume (boundaryStrips d j (Real.sqrt d * (3 : ℝ) ^ (r + 1))) := by
        rw [Transport.volume_image_affine, Matrix.det_one, abs_one, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (2 * (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ (r + 1)) *
          ((3 : ℝ) ^ j) ^ (d - 1)) := volume_boundaryStrips_le j (by positivity)
      _ = _ := by
        congr 1
        dsimp [A, S]
        rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
        ring
  calc
    volume R = volume (R \ N) := (measure_sdiff_null hN).symm
    _ ≤ volume O + volume (⋃ w ∈ E, ⋃ i : Fin d, ⋃ b : Bool, matVecMul P '' B w i b) :=
      (measure_mono hcover).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (A * S) + ENNReal.ofReal (Cface * S) := add_le_add houter hfaces
    _ = ENNReal.ofReal ((A + Cface) * S) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    _ ≤ ENNReal.ofReal ((A + Cface + 1) * (3 : ℝ) ^ r * ((3 : ℝ) ^ j) ^ (d - 1)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc]
      change (A + Cface) * S ≤ (A + Cface + 1) * S
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by dsimp [S];
        positivity)

/-- The smaller hybrid rows satisfy the required `3^(r-j)` relative-volume
bound, with finiteness produced and one constant before all other data. -/
theorem hybrid_lower_row_relVolume_bounds (d : ℕ) (hd : 2 ≤ d) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q q' : Mat d), IsUnit q → IsUnit q' →
      gridRatio q q' ≤ K₀ → ∀ (j n r : ℤ), r < n → ∀ y : Vec d,
      let W := adaptedCellTranslate q j y
      let U := adaptedUncoveredPart W q' n
      ∃ hfin : (maximalAdaptedCellCenters U q n r).Finite,
        (∑ _z ∈ hfin.toFinset, (volume (adaptedCell q r)).toReal / (volume W).toReal) ≤
          C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hraw⟩ := volume_hybrid_lower_row_le d hd K₀ hK₀
  refine ⟨C, hC, ?_⟩
  intro q q' hq hq' hK j n r hr y W U
  have hW : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q j y
  have hU : volume U ≠ ⊤ := ne_top_of_le_ne_top hW (measure_mono Set.sdiff_subset)
  let hfin := finite_maximalAdaptedCellCenters_of_volume_ne_top hq hU n r
  have hWpos : 0 < (volume W).toReal := by
    change 0 < (volume (adaptedCellTranslate q j y)).toReal
    rw [volume_adaptedCellTranslate_toReal]
    have hdet : q.det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det q).mp hq)
    positivity
  refine ⟨hfin, ?_⟩
  apply maximalAdaptedCell_row_relVolume_le hq U n r hfin
    (ENNReal.toReal_pos_iff.mp hWpos).1.ne' hW (by positivity)
  have hscale : C * (3 : ℝ) ^ r * ((3 : ℝ) ^ j) ^ (d - 1) =
      (C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) * ((3 : ℝ) ^ j) ^ d := by
    have hdpow : ((3 : ℝ) ^ j) ^ d = ((3 : ℝ) ^ j) ^ (d - 1) * (3 : ℝ) ^ j := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ d)]
      rw [pow_add, pow_one]
    rw [hdpow, ← Int.cast_sub, Real.rpow_intCast, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    field_simp
  have himage : matVecMul q '' (⋃ w ∈ maximalAdaptedCellIndices U q n r, standardCell d r w) =
      ⋃ w ∈ maximalAdaptedCellIndices U q n r, adaptedCellAtCenter q r w := by
    simp only [Set.image_iUnion, adaptedCellAtCenter_eq_affine_standardCell]
  calc
    volume (⋃ w ∈ maximalAdaptedCellIndices U q n r, adaptedCellAtCenter q r w) =
        ENNReal.ofReal |q.det| *
          volume (⋃ w ∈ maximalAdaptedCellIndices U q n r, standardCell d r w) := by
      rw [← himage]
      simpa only [zero_add] using Transport.volume_image_affine q (0 : Vec d)
        (⋃ w ∈ maximalAdaptedCellIndices U q n r, standardCell d r w)
    _ ≤ ENNReal.ofReal |q.det| *
        ENNReal.ofReal (C * (3 : ℝ) ^ r * ((3 : ℝ) ^ j) ^ (d - 1)) :=
      mul_le_mul_right (hraw q q' hq hq' hK j n r hr y) _
    _ = ENNReal.ofReal (C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) * volume W := by
      rw [hscale, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by positivity), volume_adaptedCellTranslate]
      ring

/-- Complete construction (ii), including the cap and every smaller row.
Neither openness nor finiteness of the uncovered set is an extra premise. -/
theorem two_grid_whitney_part_two (d : ℕ) (hd : 2 ≤ d) (K₀ : ℝ) (hK₀ : 1 ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q q' : Mat d), IsUnit q → IsUnit q' →
      gridRatio q q' ≤ K₀ → ∀ (j n : ℤ), ∀ y : Vec d,
      let W := adaptedCellTranslate q j y
      let U := adaptedUncoveredPart W q' n
      ∃ hfin : ∀ r : ℤ, r ≤ n → (maximalAdaptedCellCenters U q n r).Finite,
        (∀ (r : ℤ) (w : Fin d → ℤ), IsMaximalAdaptedCellIn U q n r w →
          adaptedCellAtCenter q r w ⊆ U) ∧
        Set.PairwiseDisjoint {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn U q n p.1 p.2}
          (fun p => adaptedCellAtCenter q p.1 p.2) ∧
        volume (W \ (adaptedCoveredPart W q' n ∪
          ⋃ p ∈ {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn U q n p.1 p.2},
            adaptedCellAtCenter q p.1 p.2)) = 0 ∧
        (∀ (r : ℤ) (hr : r ≤ n),
          (∑ _z ∈ (hfin r hr).toFinset,
            (volume (adaptedCell q r)).toReal / (volume W).toReal) ≤
              C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C₁, hC₁, hlower⟩ := hybrid_lower_row_relVolume_bounds d hd K₀ hK₀
  let A : ℝ := 2 * (d : ℝ) * K₀ * Real.sqrt d
  refine ⟨max C₁ A, hC₁.trans_le (le_max_left _ _), ?_⟩
  intro q q' hq hq' hK j n y W U
  obtain ⟨hfin, hsub, hdis, hnull, hcap⟩ := hybrid_whitney_partition_cap hd hK₀ hq hq' hK j n y
  refine ⟨hfin, hsub, hdis, hnull, ?_⟩
  intro r hr
  rcases lt_or_eq_of_le hr with hlt | rfl
  · obtain ⟨_hfin, hbound⟩ := hlower q q' hq hq' hK j n r hlt y
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact hcap.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end HCPolySupport.HighContrast.Geometry

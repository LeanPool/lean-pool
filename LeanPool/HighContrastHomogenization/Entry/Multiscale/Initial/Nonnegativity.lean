/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.SourceBounds

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.Nonnegativity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: nonnegativity and order on the Euclidean grid

The profile, its fluctuation and mean histories, and the determinant drift are nonnegative
at the Euclidean grid, and the normalized mean is antitone in its left generation.  These
are the order facts the crude bound of `p.initial.fixed.grid.scale`
and the logarithmic decrement `e.initial.log.decrement` consume.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-! ## C. Nonnegativity and order on the Euclidean grid -/

/-- C1. The fluctuation history is a nonnegative real. -/
theorem fluctuationHistory_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d)
    (jStar : ℕ) (m : ℤ) :
    0 ≤ fluctuationHistory P γ q jStar m := by
  rw [fluctuationHistory]
  apply integral_nonneg
  intro a
  apply Real.iSup_nonneg
  intro j
  apply Real.iSup_nonneg
  intro hj
  apply mul_nonneg
  · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  · apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro hz
    exact pow_nonneg (norm_nonneg _) _

/-- C3. `P^Id_{j,m}` is antitone in the first index (congruence of the annealed order). -/
theorem normalizedMean_one_antitone_left (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (Src : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K Src →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ i j m : ℤ, (jStar : ℤ) ≤ i → i ≤ j →
          BlockMatLoewnerLE (relMean P (1 : Mat d) j m)
            (relMean P (1 : Mat d) i m) := by
  intro P E Ψ K Src hP hstat _hunit hdag jStar hjStar i j m hi hij
  have := hP
  have : NeZero d := ⟨by omega⟩
  have hAi : Matrix.PosDef (HCPolySupport.toFullBlockMat (HCPolySupport.HighContrast.adaptedMean
    P (1 : Mat d) i)) := by
    have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat
      hdag jStar hjStar
      (1 : Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) i
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
  have hAj : Matrix.PosDef (HCPolySupport.toFullBlockMat (HCPolySupport.HighContrast.adaptedMean
    P (1 : Mat d) j)) := by
    have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat
      hdag jStar hjStar
      (1 : Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) j
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
  have hAm : Matrix.PosDef (HCPolySupport.toFullBlockMat (HCPolySupport.HighContrast.adaptedMean
    P (1 : Mat d) m)) := by
    have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat
      hdag jStar hjStar
      (1 : Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) m
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
  have hanti : HCPolySupport.BlockMatLoewnerLE
      (HCPolySupport.HighContrast.adaptedMean P (1 : Mat d) j)
        (HCPolySupport.HighContrast.adaptedMean P (1 : Mat d) i) := by
    have h := HCPolySupport.HighContrast.Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat
      hdag jStar hjStar
      (1 : Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) i j hi hij
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
  set Ai := HCPolySupport.HighContrast.adaptedMean P (1 : Mat d) i
  set Aj := HCPolySupport.HighContrast.adaptedMean P (1 : Mat d) j
  set Am := HCPolySupport.HighContrast.adaptedMean P (1 : Mat d) m
  have hraw : HCPolySupport.toFullBlockMat Aj ≤ HCPolySupport.toFullBlockMat Ai :=
    (HCPolySupport.HighContrast.Annealed.fullBlock_le_iff hAj.isHermitian hAi.isHermitian).mpr hanti
  have hdiff : (HCPolySupport.toFullBlockMat Ai - HCPolySupport.toFullBlockMat Aj).PosSemidef :=
    Matrix.le_iff.mp hraw
  set T := HCPolySupport.HighContrast.matSqrt (HCPolySupport.toFullBlockMat Am)⁻¹
  have hTposdef : T.PosDef := HCPolySupport.HighContrast.Multiscale.matSqrt_inv_posDef_full hAm
  have hT : T.IsHermitian := hTposdef.isHermitian
  have hstep : Matrix.PosSemidef
      (T * HCPolySupport.toFullBlockMat Ai * T - T * HCPolySupport.toFullBlockMat Aj * T) := by
    have hcm := Matrix.PosSemidef.conjTranspose_mul_mul_same hdiff T
    simpa only [hT.eq, mul_sub, sub_mul] using hcm
  have hfinal : T * HCPolySupport.toFullBlockMat Aj * T ≤ T * HCPolySupport.toFullBlockMat Ai * T :=
    Matrix.le_iff.mpr hstep
  have hHj : Matrix.PosDef (HCPolySupport.toFullBlockMat
    (HCPolySupport.HighContrast.normalizedBlock Aj Am)) :=
    HCPolySupport.HighContrast.Annealed.normalizedBlock_posDef Aj Am hAj hAm
  have hHi : Matrix.PosDef (HCPolySupport.toFullBlockMat
    (HCPolySupport.HighContrast.normalizedBlock Ai Am)) :=
    HCPolySupport.HighContrast.Annealed.normalizedBlock_posDef Ai Am hAi hAm
  have hgoal : HCPolySupport.toFullBlockMat (HCPolySupport.HighContrast.normalizedBlock Aj Am)
      ≤ HCPolySupport.toFullBlockMat (HCPolySupport.HighContrast.normalizedBlock Ai Am) := by
    unfold HCPolySupport.HighContrast.normalizedBlock
    simp only [HCPolySupport.toFullBlockMat_ofFullBlockMat]
    exact hfinal
  exact (HCPolySupport.HighContrast.Annealed.fullBlock_le_iff hHj.isHermitian
    hHi.isHermitian).mp hgoal

/-- C4. The Euclidean drift is nonnegative (`p.initial.fixed.grid.scale`). -/
theorem determinantDrift_one_nonneg (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (Src : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K Src →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ m : ℤ, 0 ≤ determinantDrift P γ (1 : Mat d) jStar m := by
  intro P E Ψ K Src hP hstat _hunit hdag jStar hjStar m
  have := hP
  have : NeZero d := ⟨by omega⟩
  unfold HCPolySupport.HighContrast.determinantDrift
  apply Finset.sum_nonneg
  intro j hj
  have hjlo : (jStar : ℤ) + 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hi : (jStar : ℤ) ≤ j - 1 := by omega
  apply mul_nonneg
  · exact Real.rpow_nonneg (by norm_num) _
  · have hAi : Matrix.PosDef (HCPolySupport.toFullBlockMat
        (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) (j - 1))) := by
      have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
        jStar hjStar (1 : HCPolySupport.Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef
          d) (j - 1)
      rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
    have hAj : Matrix.PosDef (HCPolySupport.toFullBlockMat
        (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) j)) := by
      have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
        jStar hjStar (1 : HCPolySupport.Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) j
      rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
    have hAm : Matrix.PosDef (HCPolySupport.toFullBlockMat
        (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) m)) := by
      have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
        jStar hjStar (1 : HCPolySupport.Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) m
      rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
    have hanti : HCPolySupport.BlockMatLoewnerLE
        (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) j)
        (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) (j - 1)) := by
      have h := HCPolySupport.HighContrast.Annealed.adaptedMean_antitone d hd P γ E Ψ K Src
        hstat hdag
        jStar hjStar (1 : HCPolySupport.Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef
          d) (j - 1) j hi (by omega)
      rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
    set Ai := HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) (j - 1)
    set Aj := HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) j
    set Am := HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) m
    have hraw : HCPolySupport.toFullBlockMat Aj ≤ HCPolySupport.toFullBlockMat Ai :=
      (HCPolySupport.HighContrast.Annealed.fullBlock_le_iff hAj.isHermitian hAi.isHermitian).mpr
        hanti
    have hdiff : (HCPolySupport.toFullBlockMat Ai - HCPolySupport.toFullBlockMat Aj).PosSemidef :=
      Matrix.le_iff.mp hraw
    set T := HCPolySupport.HighContrast.matSqrt (HCPolySupport.toFullBlockMat Am)⁻¹
    have hTposdef : T.PosDef := HCPolySupport.HighContrast.Multiscale.matSqrt_inv_posDef_full hAm
    have hT : T.IsHermitian := hTposdef.isHermitian
    have hstep : Matrix.PosSemidef
        (T * HCPolySupport.toFullBlockMat Ai * T - T * HCPolySupport.toFullBlockMat Aj * T) := by
      have hcm := Matrix.PosSemidef.conjTranspose_mul_mul_same hdiff T
      simpa only [hT.eq, mul_sub, sub_mul] using hcm
    have hle : HCPolySupport.toFullBlockMat (relMean P (1 : HCPolySupport.Mat d) j m) ≤
        HCPolySupport.toFullBlockMat (relMean P (1 : HCPolySupport.Mat d) (j - 1) m) := by
      have hfinal : T * HCPolySupport.toFullBlockMat Aj * T ≤ T * HCPolySupport.toFullBlockMat
        Ai * T :=
        Matrix.le_iff.mpr hstep
      simpa [relMean, HCPolySupport.HighContrast.normalizedBlock, Ai, Aj, Am,
        HCPolySupport.toFullBlockMat_ofFullBlockMat] using hfinal
    have hpsd : (HCPolySupport.toFullBlockMat (relMean P (1 : HCPolySupport.Mat d) (j - 1) m) -
        HCPolySupport.toFullBlockMat (relMean P (1 : HCPolySupport.Mat d) j m)).PosSemidef :=
      Matrix.le_iff.mp hle
    unfold HCPolySupport.HighContrast.blockTrace
    rw [HCPolySupport.HighContrast.Recurrence.toFullBlockMat_blockSub]
    exact hpsd.trace_nonneg

/-- C5. The Euclidean profile is nonnegative. -/
theorem profile_one_nonneg (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (Src : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K Src →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
          0 ≤ profile P γ (1 : Mat d) jStar n m := by
  intro P E Ψ K Src hP hstat _hunit hdag jStar hjStar n m hn hnm
  have : IsProbabilityMeasure P := hP
  let : NeZero d := ⟨by omega⟩
  have hQ1 : (1 : ℝ) ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (bigQ_two_le d γ hγ))
  have hmean :
      ∀ n' m' : ℤ, (jStar : ℤ) ≤ n' →
        0 ≤ meanHistory P γ (1 : Mat d) n' m' := by
    intro n' m' hn'
    rw [meanHistory]
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    · obtain ⟨hnj, hjm⟩ := Finset.mem_Ico.mp hj
      have hF := Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
        jStar hjStar (1 : Mat d) (Geometry.one_posDef d) j
      have hG := Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
        jStar hjStar (1 : Mat d) (Geometry.one_posDef d) m'
      have hGF := Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hdag
        jStar hjStar (1 : Mat d) (Geometry.one_posDef d) j m' (hn'.trans hnj)
        (le_of_lt hjm)
      have horder := Annealed.normalizedBlock_order_consequences (bigQ d γ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) j)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) m') hF hG hGF
      simpa only [relMean, Geometry.explicitRoundedGrid_one] using horder.2.2.2.2.2
  have hpen :
      0 ≤ meanPenalty (bigQ d γ) (relMean P (1 : Mat d) n m) := by
    have hF := Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : Mat d) (Geometry.one_posDef d) n
    have hG := Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : Mat d) (Geometry.one_posDef d) m
    have hGF := Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : Mat d) (Geometry.one_posDef d) n m hn hnm
    have horder := Annealed.normalizedBlock_order_consequences (bigQ d γ)
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n)
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) m) hF hG hGF
    simpa only [relMean, Geometry.explicitRoundedGrid_one] using horder.2.2.2.2.2
  have hfluc_n : 0 ≤ fluctuationHistory P γ (1 : Mat d) jStar n := by
    rw [fluctuationHistory]
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro hj
    apply mul_nonneg
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    · apply Real.iSup_nonneg
      intro z
      apply Real.iSup_nonneg
      intro hz
      exact pow_nonneg (norm_nonneg _) _
  have hhist : 0 ≤ history P γ (1 : Mat d) jStar n := by
    rw [history]
    exact add_nonneg hfluc_n (hmean (jStar : ℤ) n le_rfl)
  have hint :
      ∀ j : ℤ,
        0 ≤
          ∫ a,
            absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P (1 : Mat d) j a) ^
              bigQ d γ ∂P := by
    intro j
    have hsym :
        ∀ᵐ a ∂P, IsSymmetricBlockMat (normalizedFluctuationSelf P (1 : Mat d) j a) := by
      have hmem :=
        Annealed.memLqSchatten_normalizedFluctuation d hd P γ E Ψ K Src hstat hdag
          jStar hjStar (1 : Mat d) (Geometry.one_posDef d) j j 0
          (bigQ d γ : ℝ) hQ1
      simpa [Geometry.explicitRoundedGrid_one, normalizedFluctuationSelf] using hmem.symmetric
    apply integral_nonneg_of_ae
    exact hsym.mono fun a ha =>
      pow_nonneg
        (Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff _).2 ha) hQ1)
        _
  rw [profile]
  apply add_nonneg
  · apply add_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
        · linarith only [hpen]
      · exact hhist
    · exact hmean n m hn
  · apply Finset.sum_nonneg
    intro j hj
    repeat' apply mul_nonneg
    · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    · exact Real.exp_nonneg _
    · exact hint j

end

end HCPolySupport.HighContrast.Multiscale

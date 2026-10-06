/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.Nonnegativity
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.CrudeProfile

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: Step 1, the crude profile bound

Step 1 of the printed proof (`p.initial.fixed.grid.scale`):
at the Euclidean grid and the seed generation `j_*` the mean history, the determinant drift
and the profile are each bounded by `C (2 + Π)^N` with `C` and `N` depending only on `d`
and `γ`.  The seed bound needs only the single-cell fluctuation history at `j_*`, not the
fluctuation history at a general generation.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockSub blockTrace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-! ## D. Step 1 — the crude profile bound (`p.initial.fixed.grid.scale`) -/

/-- Symmetry of the Euclidean normalized mean at any two scales. -/
private theorem normalizedMean_one_isSymm {d : ℕ} (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K Src) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (j m : ℤ) : IsSymmetricBlockMat (relMean P (1 : Mat d) j m) := by
  have : NeZero d := ⟨by omega⟩
  have hAj : Matrix.PosDef (toFullBlockMat (adaptedMean P (1 : Mat d) j)) := by
    have h := Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) j
    rwa [Geometry.explicitRoundedGrid_one] at h
  have hAm : Matrix.PosDef (toFullBlockMat (adaptedMean P (1 : Mat d) m)) := by
    have h := Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) m
    rwa [Geometry.explicitRoundedGrid_one] at h
  exact (Analysis.toFullBlockMat_isHermitian_iff _).1
    (Annealed.normalizedBlock_posDef _ _ hAj hAm).isHermitian

/-- D1. `ℋ^mean_Id(m;n) ≤ C(2+Π)^C` (`p.initial.fixed.grid.scale`). -/
theorem meanHistory_one_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
            meanHistory P γ (1 : Mat d) n m ≤
              ((1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ - 1) *
                (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ := by
  obtain ⟨Csrc, hCsrc, hnorm⟩ := initial_normalization_bounds_all d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr n m hn hnm
  have := hP
  have : NeZero d := ⟨by omega⟩
  have hPi : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hc : (1 : ℝ) ≤ 24 * aspectRatio E := by linarith only [hPi]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hbase : (1 : ℝ) ≤ 1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1) :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hdnn) (sub_nonneg.mpr hc))
  have hB : (0 : ℝ) ≤ (1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ - 1 := by
    have := one_le_pow₀ (n := bigQ d γ) hbase
    linarith only [this]
  have hθ : (0 : ℝ) < (1 - γ) / 4 := by
    have := hγ.2
    linarith only [this]
  have hstep : ∀ j ∈ Finset.Ico n m,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
          meanPenalty (bigQ d γ) (relMean P (1 : Mat d) j m) ≤
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
          ((1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ - 1) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    have hjs : (jStar : ℤ) ≤ j := le_trans hn hj1
    have hjm : j ≤ m := le_of_lt hj2
    obtain ⟨-, -, hIM, hMc, -⟩ := hnorm P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr j m
      hjs hjm
    have hsymm := normalizedMean_one_isSymm hd γ P E Ψ K Src hstat hdag jStar hjStar j m
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    exact meanPenalty_le_of_le_scale (bigQ d γ) _ hsymm (24 * aspectRatio E) hc hIM hMc
  calc meanHistory P γ (1 : Mat d) n m
      = ∑ j ∈ Finset.Ico n m,
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
            meanPenalty (bigQ d γ) (relMean P (1 : Mat d) j m) := rfl
    _ ≤ ∑ j ∈ Finset.Ico n m,
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
            ((1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ - 1) :=
        Finset.sum_le_sum hstep
    _ = (∑ j ∈ Finset.Ico n m, (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ)))) *
          ((1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ - 1) := by
        rw [Finset.sum_mul]
    _ ≤ (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ *
          ((1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ - 1) :=
        mul_le_mul_of_nonneg_right (geometric_weight_sum_Ico_le ((1 - γ) / 4) hθ n m) hB
    _ = ((1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ - 1) *
          (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ := by ring

/-- D2. `D_{Id,j_*}(m) ≤ tr(P^Id_{j_*,m} − I) ≤ CΠ` (`p.initial.fixed.grid.scale`). -/
theorem determinantDrift_one_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ m : ℤ, (jStar : ℤ) ≤ m →
            determinantDrift P γ (1 : Mat d) jStar m ≤
              2 * (d : ℝ) * (24 * aspectRatio E - 1) := by
  obtain ⟨Csrc, hCsrc, hnorm⟩ := initial_normalization_bounds_all d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr m hm
  have := hP
  have : NeZero d := ⟨by omega⟩
  have hanti := normalizedMean_one_antitone_left d hd γ hγ P E Ψ K Src hP hstat hunit hdag
    jStar hjStar
  have hsub : ∀ A B : BlockMat d, blockTrace (blockSub A B) = blockTrace A - blockTrace B := by
    intro A B
    unfold blockTrace
    rw [Recurrence.toFullBlockMat_blockSub, Matrix.trace_sub]
  have hsymm : ∀ j : ℤ, IsSymmetricBlockMat (relMean P (1 : Mat d) j m) := fun j =>
    normalizedMean_one_isSymm hd γ P E Ψ K Src hstat hdag jStar hjStar j m
  have htnn : ∀ i j : ℤ, (jStar : ℤ) ≤ i → i ≤ j →
      0 ≤ blockTrace (blockSub (relMean P (1 : Mat d) i m)
        (relMean P (1 : Mat d) j m)) := by
    intro i j hi hij
    have hle := hanti i j m hi hij
    have hHi : (toFullBlockMat (relMean P (1 : Mat d) i m)).IsHermitian :=
      (Analysis.toFullBlockMat_isHermitian_iff _).2 (hsymm i)
    have hHj : (toFullBlockMat (relMean P (1 : Mat d) j m)).IsHermitian :=
      (Analysis.toFullBlockMat_isHermitian_iff _).2 (hsymm j)
    have hraw : toFullBlockMat (relMean P (1 : Mat d) j m) ≤
        toFullBlockMat (relMean P (1 : Mat d) i m) :=
      (Annealed.fullBlock_le_iff hHj hHi).mpr hle
    have hpsd := Matrix.le_iff.mp hraw
    unfold blockTrace
    rw [Recurrence.toFullBlockMat_blockSub]
    exact hpsd.trace_nonneg
  have hθ : (0 : ℝ) < (1 - γ) / 8 := by
    have := hγ.2
    linarith only [this]
  -- Step 1: drop the weights.
  have hstep1 : determinantDrift P γ (1 : Mat d) jStar m ≤
      ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
        (blockTrace (relMean P (1 : Mat d) (j - 1) m) -
          blockTrace (relMean P (1 : Mat d) j m)) := by
    unfold determinantDrift
    refine Finset.sum_le_sum ?_
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hi : (jStar : ℤ) ≤ j - 1 := by omega
    have hij : j - 1 ≤ j := by omega
    have ht := htnn (j - 1) j hi hij
    have hw : (3 : ℝ) ^ (-((1 - γ) / 8) * ((m : ℝ) - (j : ℝ))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hjm : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj2
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ.le) (sub_nonneg.mpr hjm)
    rw [← hsub]
    exact mul_le_of_le_one_left ht hw
  -- Step 2: telescope.
  have hstep2 : (∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
        (blockTrace (relMean P (1 : Mat d) (j - 1) m) -
          blockTrace (relMean P (1 : Mat d) j m))) =
      blockTrace (relMean P (1 : Mat d) (jStar : ℤ) m) -
        blockTrace (relMean P (1 : Mat d) m m) :=
    sum_Icc_int_telescope (fun j => blockTrace (relMean P (1 : Mat d) j m)) hm
  -- Step 3: the endpoint is the identity.
  have hend : relMean P (1 : Mat d) m m = Book.Ch02.blockIdentity d := by
    have h := Annealed.normalizedMean_self d hd P γ E Ψ K Src hstat hdag jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) m
    rwa [Geometry.explicitRoundedGrid_one] at h
  -- Step 4: the remaining trace excess.
  obtain ⟨-, -, -, hMc, -⟩ :=
    hnorm P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr (jStar : ℤ) m le_rfl hm
  have hfin := blockTrace_sub_identity_le_of_le_scale
    (relMean P (1 : Mat d) (jStar : ℤ) m) (24 * aspectRatio E) hMc
  rw [hsub] at hfin
  rw [hstep2, hend] at hstep1
  linarith only [hstep1, hfin]

/-- D3. The seed term of `𝒫_Id(m;j_*)` (`p.initial.fixed.grid.scale`). -/
theorem profile_one_seed_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ m : ℤ, (jStar : ℤ) ≤ m →
            (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - ((jStar : ℤ) : ℝ))) *
                  (1 + meanPenalty (bigQ d γ) (relMean P (1 : Mat d) (jStar : ℤ) m)) *
                history P γ (1 : Mat d) jStar (jStar : ℤ) ≤
              (1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ *
                (2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ bigQ d γ)) := by
  obtain ⟨Cnorm, hCnorm, hnorm⟩ := initial_normalization_bounds_all d hd γ hγ
  obtain ⟨Cmom, hCmom, hmom⟩ := normalizedFluctuationSelf_one_moment_le d hd γ hγ
  refine ⟨max Cnorm Cmom, lt_of_lt_of_le hCnorm (le_max_left _ _), ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr m hm
  have := hP
  have : NeZero d := ⟨by omega⟩
  have hK : (1 : ℝ) < K := hdag.one_lt_growthWitness
  have hthrN : ⌈Cnorm * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK Cnorm (max Cnorm Cmom) (le_max_left _ _) _ hthr
  have hthrM : ⌈Cmom * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK Cmom (max Cnorm Cmom) (le_max_right _ _) _ hthr
  have hPi : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hc : (1 : ℝ) ≤ 24 * aspectRatio E := by linarith only [hPi]
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hbase : (1 : ℝ) ≤ 1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1) :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hdnn) (sub_nonneg.mpr hc))
  have hB1 : (1 : ℝ) ≤ (1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ :=
    one_le_pow₀ hbase
  -- The mean factor.
  obtain ⟨-, -, hIM, hMc, -⟩ :=
    hnorm P E Ψ K Src hP hstat hunit hdag jStar hjStar hthrN (jStar : ℤ) m le_rfl hm
  have hsymm := normalizedMean_one_isSymm hd γ P E Ψ K Src hstat hdag jStar hjStar (jStar : ℤ) m
  have hmp := meanPenalty_le_of_le_scale (bigQ d γ)
    (relMean P (1 : Mat d) (jStar : ℤ) m) hsymm (24 * aspectRatio E) hc hIM hMc
  have hmp0 : 0 ≤ 1 + meanPenalty (bigQ d γ) (relMean P (1 : Mat d) (jStar : ℤ) m) := by
    have ht := Analysis.blockTrace_identity_sub_nonneg
      (relMean P (1 : Mat d) (jStar : ℤ) m) hsymm hIM
    have := one_le_pow₀ (n := bigQ d γ)
      (show (1 : ℝ) ≤ 1 + blockTrace (blockSub (relMean P (1 : Mat d) (jStar : ℤ) m)
        (Book.Ch02.blockIdentity d)) by linarith only [ht])
    simp only [meanPenalty]
    linarith only [this]
  -- The history factor.
  have hhist : history P γ (1 : Mat d) jStar (jStar : ℤ) =
      fluctuationHistory P γ (1 : Mat d) jStar (jStar : ℤ) := by
    simp [history, meanHistory]
  have hH0 : 0 ≤ history P γ (1 : Mat d) jStar (jStar : ℤ) := by
    rw [hhist]
    exact fluctuationHistory_nonneg P γ (1 : Mat d) jStar (jStar : ℤ)
  have hHle : history P γ (1 : Mat d) jStar (jStar : ℤ) ≤
      2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ bigQ d γ) := by
    rw [hhist]
    refine le_trans (fluctuationHistory_one_jStar_le_moment d hd γ hγ P E Ψ K Src hP hstat
      hunit hdag jStar hjStar) ?_
    exact hmom P E Ψ K Src hP hstat hunit hdag jStar hjStar hthrM (jStar : ℤ) le_rfl
  -- The weight.
  have hw1 : (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - ((jStar : ℤ) : ℝ))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hjm : (((jStar : ℤ)) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hγ1 : γ < 1 := hγ.2
    have hθ4 : (0 : ℝ) ≤ (1 - γ) / 4 := div_nonneg (sub_nonneg.mpr hγ1.le) (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ4) (sub_nonneg.mpr hjm)
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - ((jStar : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  -- Assemble.
  have hfirst : (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - ((jStar : ℤ) : ℝ))) *
      (1 + meanPenalty (bigQ d γ) (relMean P (1 : Mat d) (jStar : ℤ) m)) ≤
      (1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ bigQ d γ := by
    refine le_trans (mul_le_of_le_one_left hmp0 hw1) ?_
    linarith only [hmp]
  refine mul_le_mul hfirst hHle hH0 (le_trans zero_le_one hB1)

/-- D4. The new-fluctuation sum of `𝒫_Id(m;j_*)` (`p.initial.fixed.grid.scale`). -/
theorem profile_one_fluct_sum_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ m : ℤ, (jStar : ℤ) ≤ m →
            (∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
                (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
                    Real.exp ((bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m) *
                  ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                    (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P) ≤
              (24 * aspectRatio E) ^ (2 * d * bigQ d γ) *
                  (2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ bigQ d γ)) *
                (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ := by
  obtain ⟨Cnorm, hCnorm_pos, hnorm⟩ := initial_normalization_bounds_all d hd γ hγ
  obtain ⟨Cmom, _, hmom⟩ := normalizedFluctuationSelf_one_moment_le d hd γ hγ
  refine ⟨max Cnorm Cmom, lt_of_lt_of_le hCnorm_pos (le_max_left _ _), ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hceil m hm
  have : IsProbabilityMeasure P := hP
  have : NeZero d := ⟨by omega⟩
  have hceil_norm : ⌈Cnorm * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cnorm (max Cnorm Cmom)
      (le_max_left _ _) (jStar : ℤ) hceil
  have hceil_mom : ⌈Cmom * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hdag.one_lt_growthWitness Cmom (max Cnorm Cmom)
      (le_max_right _ _) (jStar : ℤ) hceil
  have hPi_pos : (0 : ℝ) < 24 * aspectRatio E := by
    have hPi : (1 : ℝ) ≤ aspectRatio E :=
      HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
    exact mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one hPi)
  have hQpos : (0 : ℝ) < (bigQ d γ : ℝ) :=
    HCPolySupport.HighContrast.Multiscale.bigQ_real_pos d γ hγ
  have hQone : (1 : ℝ) ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2)
      (HCPolySupport.HighContrast.Multiscale.bigQ_two_le d γ hγ))
  have htheta_pos : 0 < (1 - γ) / 4 := by
    rcases hγ with ⟨hγ0, hγ1⟩
    linarith only [hγ1]
  let B : ℝ := (24 * aspectRatio E) ^ (2 * d * bigQ d γ)
  let A : ℝ := 2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ bigQ d γ)
  have hBnn : 0 ≤ B := by
    dsimp [B]
    exact pow_nonneg hPi_pos.le _
  have hAnn : 0 ≤ A := by
    dsimp [A]
    positivity
  have hBAnn : 0 ≤ B * A := mul_nonneg hBnn hAnn
  have hsummand :
      ∀ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
              Real.exp ((bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m) *
            ∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P
          ≤
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) * (B * A) := by
    intro j hj
    have hjbounds := Finset.mem_Icc.mp hj
    have hjle : (jStar : ℤ) ≤ j := by linarith only [hjbounds.1]
    have hjm : j ≤ m := hjbounds.2
    have hlog :
        detIncrement P (1 : Mat d) j m ≤
          2 * (d : ℝ) * Real.log (24 * aspectRatio E) :=
      (hnorm P E Ψ K Src hP hstat hunit hdag jStar hjStar hceil_norm j m hjle hjm).2.2.2.2.2
    have hmoment :
        (∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P) ≤ A := by
      dsimp [A]
      exact hmom P E Ψ K Src hP hstat hunit hdag jStar hjStar hceil_mom j hjle
    have hexp :
        Real.exp ((bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m) ≤ B := by
      have hmul :
          (bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m ≤
            (bigQ d γ : ℝ) * (2 * (d : ℝ) * Real.log (24 * aspectRatio E)) :=
        mul_le_mul_of_nonneg_left hlog hQpos.le
      refine (Real.exp_le_exp.mpr hmul).trans_eq ?_
      dsimp [B]
      have hcast :
          (bigQ d γ : ℝ) * (2 * (d : ℝ) * Real.log (24 * aspectRatio E)) =
            ((2 * d * bigQ d γ : ℕ) : ℝ) * Real.log (24 * aspectRatio E) := by
        push_cast
        ring
      rw [hcast, Real.exp_nat_mul, Real.exp_log hPi_pos]
    have hweight : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hmoment_nonneg :
        0 ≤ ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P := by
      have hmem := HCPolySupport.HighContrast.Annealed.memLqSchatten_normalizedFluctuation
        d hd P γ E Ψ K Src hstat hdag jStar hjStar (1 : Mat d)
        (HCPolySupport.HighContrast.Geometry.one_posDef d) j j 0 (bigQ d γ : ℝ) hQone
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hmem.symmetric] with a ha
      have hsym : IsSymmetricBlockMat (normalizedFluctuationSelf P (1 : Mat d) j a) := by
        simpa [normalizedFluctuationSelf,
          HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] using ha
      exact pow_nonneg
        (HCPolySupport.HighContrast.Analysis.absSchattenNorm_nonneg
          ((HCPolySupport.HighContrast.Analysis.toFullBlockMat_isHermitian_iff _).2 hsym) hQone) _
    have hcore :
        Real.exp ((bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m) *
            (∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P) ≤ B * A :=
      mul_le_mul hexp hmoment hmoment_nonneg hBnn
    calc
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
              Real.exp ((bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m) *
            ∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P
          = (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
              (Real.exp ((bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m) *
            ∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P) := by ring
      _ ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) * (B * A) :=
          mul_le_mul_of_nonneg_left hcore hweight
  have hsum := Finset.sum_le_sum hsummand
  calc
    (∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
            Real.exp ((bigQ d γ : ℝ) * detIncrement P (1 : Mat d) j m) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P)
      ≤ ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) * (B * A) := hsum
    _ = (∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ)))) * (B * A) := by
          rw [Finset.sum_mul]
    _ ≤ (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ * (B * A) :=
      mul_le_mul_of_nonneg_right
        (geometric_weight_sum_Icc_le ((1 - γ) / 4) htheta_pos ((jStar : ℤ) + 1) m) hBAnn
    _ = (24 * aspectRatio E) ^ (2 * d * bigQ d γ) *
          (2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ bigQ d γ)) *
        (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ := by
          dsimp [B, A]
          ring

/-- Raising the exponent of a base `≥ 1` only increases a nonnegative multiple. -/
private theorem le_const_mul_pow {X a c : ℝ} (hX : 1 ≤ X) (hc : 0 ≤ c) {k N : ℕ} (hk : k ≤ N)
    (h : a ≤ c * X ^ k) : a ≤ c * X ^ N :=
  h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hk) hc)

/-- D5. `e.initial.crude.profile`: `𝒫_Id(m;j_*) + D_{Id,j_*}(m) ≤ C(2+Π)^N`. -/
theorem initial_crude_profile (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∃ N : ℕ,
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (Src : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K Src →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ m : ℤ, (jStar : ℤ) ≤ m →
                profile P γ (1 : Mat d) jStar (jStar : ℤ) m +
                    determinantDrift P γ (1 : Mat d) jStar m ≤
                  C * (2 + aspectRatio E) ^ N := by
  obtain ⟨C1, hC1, hseed⟩ := profile_one_seed_le d hd γ hγ
  obtain ⟨C2, hC2, hmean⟩ := meanHistory_one_le d hd γ hγ
  obtain ⟨C3, hC3, hfluct⟩ := profile_one_fluct_sum_le d hd γ hγ
  obtain ⟨C4, hC4, hdrift⟩ := determinantDrift_one_le d hd γ hγ
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hθ : (0 : ℝ) < (1 - γ) / 4 := by
    have := hγ.2
    linarith only [this]
  have hlt : (3 : ℝ) ^ (-((1 - γ) / 4)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hθ])
  have hw : (0 : ℝ) < (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ := inv_pos.mpr (by linarith only [hlt])
  set Q := bigQ d γ with hQdef
  set w : ℝ := (1 - (3 : ℝ) ^ (-((1 - γ) / 4)))⁻¹ with hwdef
  set N : ℕ := 2 * d * Q + Q + Q with hNdef
  have hk1 : Q + Q ≤ N := by rw [hNdef, Nat.add_assoc]; exact Nat.le_add_left _ _
  have hk2 : Q ≤ N := Nat.le_add_left _ _
  have hk3 : 2 * d * Q + Q ≤ N := Nat.le_add_right _ _
  have hk4 : 1 ≤ N := le_trans (le_trans (by norm_num : (1:ℕ) ≤ 2) hQ2) hk2
  set c1 : ℝ := (1 + 48 * (d : ℝ)) ^ Q * (2 * (d : ℝ) * (1 + 24 ^ Q)) with hc1def
  set c2 : ℝ := (1 + 48 * (d : ℝ)) ^ Q * w with hc2def
  set c3 : ℝ := 24 ^ (2 * d * Q) * (2 * (d : ℝ) * (1 + 24 ^ Q)) * w with hc3def
  set c4 : ℝ := 48 * (d : ℝ) with hc4def
  have hc1 : (0 : ℝ) ≤ c1 := by rw [hc1def]; positivity
  have hc2 : (0 : ℝ) ≤ c2 := by
    rw [hc2def]; exact mul_nonneg (by positivity) hw.le
  have hc3 : (0 : ℝ) ≤ c3 := by
    rw [hc3def]; exact mul_nonneg (by positivity) hw.le
  have hc4 : (0 : ℝ) ≤ c4 := by rw [hc4def]; positivity
  refine ⟨max (max C1 C2) (max C3 C4), ?_, c1 + c2 + c3 + c4 + 1, by linarith only [hc1, hc2,
    hc3, hc4], N, ?_⟩
  · exact lt_of_lt_of_le hC1 (le_trans (le_max_left _ _) (le_max_left _ _))
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hthr m hm
  have := hP
  have : NeZero d := ⟨by omega⟩
  have hK : (1 : ℝ) < K := hdag.one_lt_growthWitness
  have hth1 : ⌈C1 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK C1 _ (le_trans (le_max_left _ _) (le_max_left _ _)) _ hthr
  have hth2 : ⌈C2 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK C2 _ (le_trans (le_max_right _ _) (le_max_left _ _)) _ hthr
  have hth3 : ⌈C3 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK C3 _ (le_trans (le_max_left _ _) (le_max_right _ _)) _ hthr
  have hth4 : ⌈C4 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK C4 _ (le_trans (le_max_right _ _) (le_max_right _ _)) _ hthr
  have hPi : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hX : (1 : ℝ) ≤ 2 + aspectRatio E := by linarith only [hPi]
  have hXQ : (1 : ℝ) ≤ (2 + aspectRatio E) ^ Q := one_le_pow₀ hX
  have hXN : (0 : ℝ) ≤ (2 + aspectRatio E) ^ N := by positivity
  -- Elementary polynomial envelopes in the aspect ratio.
  have hbaseQ : (1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ Q ≤
      (1 + 48 * (d : ℝ)) ^ Q * (2 + aspectRatio E) ^ Q := by
    have hnn : (0 : ℝ) ≤ 1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1) := by
      have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) * (24 * aspectRatio E - 1) :=
        mul_nonneg (by positivity) (by linarith only [hPi])
      linarith only [h1]
    have hle : 1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1) ≤ (1 + 48 * (d : ℝ)) * aspectRatio E := by
      have hid : (1 + 48 * (d : ℝ)) * aspectRatio E -
          (1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) = aspectRatio E - 1 + 2 * (d : ℝ) := by
        ring
      linarith only [hid, hPi, hdnn]
    exact (pow_le_pow_left₀ hnn hle Q).trans
      (aspect_pow_le_two_add_pow (aspectRatio E) hPi (1 + 48 * (d : ℝ)) (by linarith only [hdnn]) Q)
  have hmomQ : (24 * aspectRatio E) ^ Q ≤ (24 : ℝ) ^ Q * (2 + aspectRatio E) ^ Q :=
    aspect_pow_le_two_add_pow (aspectRatio E) hPi 24 (by norm_num) Q
  have hmomBig : (24 * aspectRatio E) ^ (2 * d * Q) ≤
      (24 : ℝ) ^ (2 * d * Q) * (2 + aspectRatio E) ^ (2 * d * Q) :=
    aspect_pow_le_two_add_pow (aspectRatio E) hPi 24 (by norm_num) (2 * d * Q)
  have hM : 2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q) ≤
      (2 * (d : ℝ) * (1 + 24 ^ Q)) * (2 + aspectRatio E) ^ Q := by
    have hin : 1 + (24 * aspectRatio E) ^ Q ≤ (1 + 24 ^ Q) * (2 + aspectRatio E) ^ Q := by
      calc 1 + (24 * aspectRatio E) ^ Q
          ≤ (2 + aspectRatio E) ^ Q + (24 : ℝ) ^ Q * (2 + aspectRatio E) ^ Q := by linarith only
            [hmomQ, hXQ]
        _ = (1 + 24 ^ Q) * (2 + aspectRatio E) ^ Q := by ring
    calc 2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q)
        ≤ 2 * (d : ℝ) * ((1 + 24 ^ Q) * (2 + aspectRatio E) ^ Q) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = (2 * (d : ℝ) * (1 + 24 ^ Q)) * (2 + aspectRatio E) ^ Q := by ring
  have hM0 : (0 : ℝ) ≤ 2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q) := by
    have h1 : (0 : ℝ) ≤ (24 * aspectRatio E) ^ Q := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    exact mul_nonneg h2 (add_nonneg zero_le_one h1)
  -- The four printed bounds.
  have h1 := hseed P E Ψ K Src hP hstat hunit hdag jStar hjStar hth1 m hm
  have h2 := hmean P E Ψ K Src hP hstat hunit hdag jStar hjStar hth2 (jStar : ℤ) m le_rfl hm
  have h3 := hfluct P E Ψ K Src hP hstat hunit hdag jStar hjStar hth3 m hm
  have h4 := hdrift P E Ψ K Src hP hstat hunit hdag jStar hjStar hth4 m hm
  have e1 : (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - ((jStar : ℤ) : ℝ))) *
        (1 + meanPenalty Q (relMean P (1 : Mat d) (jStar : ℤ) m)) *
      history P γ (1 : Mat d) jStar (jStar : ℤ) ≤ c1 * (2 + aspectRatio E) ^ N := by
    refine le_const_mul_pow hX hc1 hk1 (h1.trans ?_)
    calc (1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ Q *
          (2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q))
        ≤ ((1 + 48 * (d : ℝ)) ^ Q * (2 + aspectRatio E) ^ Q) *
            ((2 * (d : ℝ) * (1 + 24 ^ Q)) * (2 + aspectRatio E) ^ Q) :=
          mul_le_mul hbaseQ hM hM0 (by positivity)
      _ = c1 * (2 + aspectRatio E) ^ (Q + Q) := by rw [hc1def, pow_add]; ring
  have e2 : meanHistory P γ (1 : Mat d) (jStar : ℤ) m ≤ c2 * (2 + aspectRatio E) ^ N := by
    refine le_const_mul_pow hX hc2 hk2 (h2.trans ?_)
    calc ((1 + 2 * (d : ℝ) * (24 * aspectRatio E - 1)) ^ Q - 1) * w
        ≤ ((1 + 48 * (d : ℝ)) ^ Q * (2 + aspectRatio E) ^ Q) * w :=
          mul_le_mul_of_nonneg_right (by linarith only [hbaseQ]) hw.le
      _ = c2 * (2 + aspectRatio E) ^ Q := by rw [hc2def]; ring
  have e3 : (∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
            Real.exp ((Q : ℝ) * detIncrement P (1 : Mat d) j m) *
          ∫ a, absSchattenNorm (Q : ℝ)
            (normalizedFluctuationSelf P (1 : Mat d) j a) ^ Q ∂P) ≤
      c3 * (2 + aspectRatio E) ^ N := by
    refine le_const_mul_pow hX hc3 hk3 (h3.trans ?_)
    have hstep : (24 * aspectRatio E) ^ (2 * d * Q) *
          (2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q)) ≤
        ((24 : ℝ) ^ (2 * d * Q) * (2 + aspectRatio E) ^ (2 * d * Q)) *
          ((2 * (d : ℝ) * (1 + 24 ^ Q)) * (2 + aspectRatio E) ^ Q) :=
      mul_le_mul hmomBig hM hM0 (by positivity)
    calc (24 * aspectRatio E) ^ (2 * d * Q) *
            (2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q)) * w
        ≤ (((24 : ℝ) ^ (2 * d * Q) * (2 + aspectRatio E) ^ (2 * d * Q)) *
            ((2 * (d : ℝ) * (1 + 24 ^ Q)) * (2 + aspectRatio E) ^ Q)) * w :=
          mul_le_mul_of_nonneg_right hstep hw.le
      _ = c3 * (2 + aspectRatio E) ^ (2 * d * Q + Q) := by rw [hc3def, pow_add]; ring
  have e4 : determinantDrift P γ (1 : Mat d) jStar m ≤ c4 * (2 + aspectRatio E) ^ N := by
    refine le_const_mul_pow hX hc4 hk4 (h4.trans ?_)
    rw [hc4def, pow_one]
    have hid : 48 * (d : ℝ) * (2 + aspectRatio E) -
        2 * (d : ℝ) * (24 * aspectRatio E - 1) = 98 * (d : ℝ) := by ring
    linarith only [hid, hdnn]
  have hprof : profile P γ (1 : Mat d) jStar (jStar : ℤ) m =
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - ((jStar : ℤ) : ℝ))) *
            (1 + meanPenalty Q (relMean P (1 : Mat d) (jStar : ℤ) m)) *
          history P γ (1 : Mat d) jStar (jStar : ℤ) +
        meanHistory P γ (1 : Mat d) (jStar : ℤ) m +
        ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
          (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
              Real.exp ((Q : ℝ) * detIncrement P (1 : Mat d) j m) *
            ∫ a, absSchattenNorm (Q : ℝ)
              (normalizedFluctuationSelf P (1 : Mat d) j a) ^ Q ∂P := rfl
  rw [hprof]
  have hsum := add_le_add (add_le_add (add_le_add e1 e2) e3) e4
  refine hsum.trans ?_
  have hEq : (c1 + c2 + c3 + c4 + 1) * (2 + aspectRatio E) ^ N =
      c1 * (2 + aspectRatio E) ^ N + c2 * (2 + aspectRatio E) ^ N +
        c3 * (2 + aspectRatio E) ^ N + c4 * (2 + aspectRatio E) ^ N +
        (2 + aspectRatio E) ^ N := by ring
  rw [hEq]
  linarith only [hXN]

end

end HCPolySupport.HighContrast.Multiscale

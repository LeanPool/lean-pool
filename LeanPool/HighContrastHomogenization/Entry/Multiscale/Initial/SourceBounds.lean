/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.CanonicalMetric
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio

/-!
# High-contrast homogenization: Entry.Multiscale.Initial.SourceBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initialization: source and normalization bounds on the unrestricted window

`HCPoly/Entry/Annealed/ReferenceNormalization.lean` carries the initial source and normalization
bounds on the window `j ≤ 2 j_*`.  The initialization places its entry generation at
`n₀ ≥ j_* + ⌈B log₃(2+Π)⌉`, unbounded relative to `j_*`, so both are restated here on the
unrestricted range `j_* ≤ j ≤ m` by re-running the source construction at `j` in place of
`j_*` (`p.initial.fixed.grid.scale`).  The single-cell sandwich and
moment bounds for the normalized self fluctuation at the Euclidean grid follow.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio blockScale
  blockSub coarseBlock isSymmetricBlockMat_coarseBlockMatrix matSqrt normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-! ## B. Source and normalization bounds on the unrestricted window
(`p.initial.fixed.grid.scale`, lifting the restriction `j ≤ 2 j_*`) -/

/-- B1. `e.initial.source.bounds`, first half, for every `j ≥ j_*`. -/
theorem initial_source_bounds_all (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ j : ℤ, (jStar : ℤ) ≤ j →
            BlockMatLoewnerLE
                (blockScale (1 / 2)
                  (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
                    toFullBlockMat (blockSwap d))))
                (adaptedMean P (1 : Mat d) j) ∧
              BlockMatLoewnerLE (adaptedMean P (1 : Mat d) j) (blockScale 2 E) := by
  obtain ⟨Csrc, hCsrc_pos, hbound⟩ := HCPolySupport.HighContrast.Annealed.initial_source_bounds
    d hd γ hγ
  refine ⟨Csrc, hCsrc_pos, ?_⟩
  intro P E Ψ K Src hP hstat _hunit hdag jStar hjStar hceil j hj
  have := hP
  have hj0 : (0:ℤ) ≤ j := le_trans (Nat.cast_nonneg jStar) hj
  have hjtoNat : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
  have hjStar_le : jStar ≤ j.toNat := by
    have h : (jStar : ℤ) ≤ (j.toNat : ℤ) := by rw [hjtoNat]; exact hj
    exact_mod_cast h
  have h2d : 2 * d ≤ 3 ^ j.toNat :=
    le_trans hjStar (Nat.pow_le_pow_right (by norm_num) hjStar_le)
  have hceil' : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (j.toNat : ℤ) :=
    le_trans hceil (by exact_mod_cast hjStar_le)
  have hwindow : j ≤ 2 * ((j.toNat : ℕ) : ℤ) := by
    rw [hjtoNat]; omega
  exact hbound P E Ψ K Src hstat hdag j.toNat h2d hceil' j hjtoNat.le hwindow

/-- B2. `e.initial.normalization.bounds` for every `j_* ≤ j ≤ m`. -/
theorem initial_normalization_bounds_all (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ j m : ℤ, (jStar : ℤ) ≤ j → j ≤ m →
            BlockMatLoewnerLE (adaptedMean P (1 : Mat d) m) (adaptedMean P (1 : Mat d) j) ∧
              BlockMatLoewnerLE (adaptedMean P (1 : Mat d) j)
                (blockScale (24 * aspectRatio E) (adaptedMean P (1 : Mat d) m)) ∧
              BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P (1 : Mat d) j m) ∧
                BlockMatLoewnerLE (relMean P (1 : Mat d) j m)
                  (blockScale (24 * aspectRatio E) (Book.Ch02.blockIdentity d)) ∧
              0 ≤ detIncrement P (1 : Mat d) j m ∧
                detIncrement P (1 : Mat d) j m ≤ 2 * (d : ℝ) * Real.log (24 * aspectRatio E) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, hCsrc_pos, hsource⟩ :=
    HCPolySupport.HighContrast.Multiscale.initial_source_bounds_all d hd γ hγ
  refine ⟨Csrc, hCsrc_pos, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hCsrcJ j m hj hjm
  have := hP
  have hjb := hsource P E Ψ K Src hP hstat hunit hdag jStar hjStar hCsrcJ j hj
  have hmb := hsource P E Ψ K Src hP hstat hunit hdag jStar hjStar hCsrcJ m (hj.trans hjm)
  have hscale_mono : ∀ {A B : HCPolySupport.BlockMat d} (c : ℝ), 0 ≤ c →
      HCPolySupport.BlockMatLoewnerLE A B →
      HCPolySupport.BlockMatLoewnerLE (HCPolySupport.HighContrast.blockScale c A)
        (HCPolySupport.HighContrast.blockScale c B) := by
    intro A B c hc hAB X
    rw [HCPolySupport.HighContrast.Source.quadratic_blockScale,
      HCPolySupport.HighContrast.Source.quadratic_blockScale]
    exact mul_le_mul_of_nonneg_left (hAB X) hc
  have htrans : ∀ {A B C : HCPolySupport.BlockMat d},
      HCPolySupport.BlockMatLoewnerLE A B → HCPolySupport.BlockMatLoewnerLE B C →
      HCPolySupport.BlockMatLoewnerLE A C := by
    intro A B C hAB hBC X
    exact (hAB X).trans (hBC X)
  have hscale_comp : ∀ (c c' : ℝ) (A : HCPolySupport.BlockMat d),
      HCPolySupport.HighContrast.blockScale c (HCPolySupport.HighContrast.blockScale c' A) =
        HCPolySupport.HighContrast.blockScale (c * c') A := by
    intro c c' A
    cases A
    simp [HCPolySupport.HighContrast.blockScale, smul_smul]
  have hone_le : (1 : ℝ) ≤ HCPolySupport.HighContrast.aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hEle := HCPolySupport.HighContrast.Annealed.refBlock_le_six_aspectRatio_smul_swapConj hdag
  have h2E := hscale_mono (2 : ℝ) (by norm_num) hEle
  rw [hscale_comp] at h2E
  have heq1 : (2 : ℝ) * (6 * HCPolySupport.HighContrast.aspectRatio E) =
      24 * HCPolySupport.HighContrast.aspectRatio E * (1 / 2) := by ring
  rw [heq1] at h2E
  have hRm := hscale_mono (24 * HCPolySupport.HighContrast.aspectRatio E)
    (mul_nonneg (by norm_num) (zero_le_one.trans hone_le)) hmb.1
  rw [hscale_comp] at hRm
  have hcomp : HCPolySupport.BlockMatLoewnerLE
      (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) j)
      (HCPolySupport.HighContrast.blockScale (24 * HCPolySupport.HighContrast.aspectRatio E)
        (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) m)) :=
    htrans hjb.2 (htrans h2E hRm)
  have hanti : HCPolySupport.BlockMatLoewnerLE
      (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) m)
      (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) j) := by
    have h := HCPolySupport.HighContrast.Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : HCPolySupport.Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d)
        j m hj hjm
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
  have horder := HCPolySupport.HighContrast.Annealed.adaptedMean_order_consequences d hd P γ E Ψ
    K Src
    hstat hdag jStar hjStar (1 : HCPolySupport.Mat d)
      (HCPolySupport.HighContrast.Geometry.one_posDef d)
    j m hj hjm
  simp only [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at horder
  obtain ⟨hIle, hlogpos, -, -, -, -⟩ := horder
  have hpj : Matrix.PosDef (HCPolySupport.toFullBlockMat
      (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) j)) := by
    have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : HCPolySupport.Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) j
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
  have hpm : Matrix.PosDef (HCPolySupport.toFullBlockMat
      (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) m)) := by
    have h := HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : HCPolySupport.Mat d) (HCPolySupport.HighContrast.Geometry.one_posDef d) m
    rwa [HCPolySupport.HighContrast.Geometry.explicitRoundedGrid_one] at h
  have hc24 : 0 < 24 * HCPolySupport.HighContrast.aspectRatio E :=
    mul_pos (by norm_num) (zero_lt_one.trans_le hone_le)
  have hfin := HCPolySupport.HighContrast.Multiscale.normalizedBlock_le_scale_and_logDet_le
    (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) j)
    (HCPolySupport.HighContrast.adaptedMean P (1 : HCPolySupport.Mat d) m)
    hpj hpm (24 * HCPolySupport.HighContrast.aspectRatio E) hc24 hcomp
  exact ⟨hanti, hcomp, hIle, hfin.1, hlogpos, hfin.2⟩

/-- B3. The source envelope of the Euclidean scale-`j` cell, `j ≥ j_*`
(`e.source.adapted.bound` at the window `j`, standard-cube clause). -/
theorem coarseBlock_one_source_envelope (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ j : ℤ, (jStar : ℤ) ≤ j →
            ∃ X : CoeffSpace d → ℝ,
              Measurable X ∧ (∀ a, 0 ≤ X a) ∧
              Integrable (fun a => X a ^ bigQ d γ) P ∧
              (∫ a, X a ^ bigQ d γ ∂P) ≤ (2 : ℝ) ^ bigQ d γ ∧
              ∀ᵐ a ∂P,
                BlockMatLoewnerLE (coarseBlock (HighContrast.adaptedCell (1 : Mat d) j) a)
                  (blockScale (X a) E) := by
  obtain ⟨Csrc, _C, hCsrc_pos, _hC_pos, hmain⟩ :=
    Source.source_multiplier_and_adapted_bound d hd γ hγ
  refine ⟨Csrc, hCsrc_pos, ?_⟩
  intro P E Ψ K Src hP hstat _hunit hdag jStar hjStar hceil j hj
  have := hP
  have hjStar_le : jStar ≤ j.toNat := by omega
  have hjStar' : 2 * d ≤ 3 ^ j.toNat :=
    le_trans hjStar (Nat.pow_le_pow_right (n := 3) (by norm_num) hjStar_le)
  have hceil' : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ ((j.toNat : ℕ) : ℤ) := by
    have h1 : ((j.toNat : ℕ) : ℤ) = j := by omega
    omega
  obtain ⟨_ell, X, _hell_meas, hX_meas, hXeq, _hae1, _hmemLp, hint, hintbound, _heLp, hae2⟩ :=
    hmain P E Ψ K Src hstat hdag j.toNat hjStar' hceil'
  refine ⟨X, hX_meas, ?_, hint, hintbound, ?_⟩
  · intro a
    rw [hXeq a]
    positivity
  · have hjle : j ≤ 2 * ((j.toNat : ℕ) : ℤ) := by omega
    have hsub : HighContrast.adaptedCell (1 : Mat d) j ⊆
        HighContrast.centeredCube d (2 * ((j.toNat : ℕ) : ℤ)) :=
      Geometry.adaptedCell_one_subset_centeredCube j hjle
    rw [Geometry.adaptedCell_one] at hsub
    have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
      have h1 : ((j.toNat : ℕ) : ℤ) = j := by omega
      exact_mod_cast h1
    have hmax : γ * max (((j.toNat : ℕ) : ℝ) - (j : ℝ)) 0 = 0 := by
      rw [hcast]
      simp
    filter_upwards [hae2] with a ha
    obtain ⟨hclause, -⟩ := ha
    have hb := hclause j 0 hsub
    rw [hmax, Real.rpow_zero, mul_one] at hb
    rw [Geometry.adaptedCell_one]
    exact hb

/-- B4 (kernel). The pathwise sandwich `−I ≤ V^Id_j ≤ 12Π X·I` of the self-normalized
fluctuation, from the envelope and `𝐄 ≤ 6Π𝐑𝐄⁻¹𝐑 ≤ 12Π 𝐀hom_{j,Id}`. -/
theorem normalizedFluctuationSelf_one_sandwich (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ j : ℤ, (jStar : ℤ) ≤ j →
            ∀ (a : CoeffSpace d) (X : ℝ), 0 ≤ X →
              BlockMatLoewnerLE (coarseBlock (HighContrast.adaptedCell (1 : Mat d) j) a)
                (blockScale X E) →
              BlockMatLoewnerLE (blockScale (-1) (Book.Ch02.blockIdentity d))
                  (normalizedFluctuationSelf P (1 : Mat d) j a) ∧
                BlockMatLoewnerLE (normalizedFluctuationSelf P (1 : Mat d) j a)
                  (blockScale (12 * aspectRatio E * X) (Book.Ch02.blockIdentity d)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, hCsrc_pos, hSrc⟩ := initial_source_bounds_all d hd γ hγ
  refine ⟨Csrc, hCsrc_pos, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hCthresh j hj a X hX hXE
  have : IsProbabilityMeasure P := hP
  obtain ⟨hRE_le_Aj, hAj_le_E2⟩ :=
    hSrc P E Ψ K Src hP hstat hunit hdag jStar hjStar hCthresh j hj
  set Aj := adaptedMean P (1 : Mat d) j with hAjdef
  set RE : BlockMat d := ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)) with hREdef
  have hAjPosDef : (toFullBlockMat Aj).PosDef := by
    have h := Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) j
    rwa [Geometry.explicitRoundedGrid_one] at h
  have hEPosDef : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hPi1 : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hREPosDef : (toFullBlockMat RE).PosDef := Analysis.swapConj_posDef hEPosDef
  have hE6RE_block : BlockMatLoewnerLE E (blockScale (6 * aspectRatio E) RE) :=
    Annealed.refBlock_le_six_aspectRatio_smul_swapConj hdag
  have hcell : HighContrast.adaptedCellTranslate (1 : Mat d) j 0 =
      HighContrast.adaptedCell (1 : Mat d) j := by
    rw [Geometry.adaptedCellTranslate_one_zero, Geometry.adaptedCell_one]
  have hSelfEq : normalizedFluctuationSelf P (1 : Mat d) j a =
      normalizedBlock (blockSub (coarseBlock (HighContrast.adaptedCell (1 : Mat d) j) a) Aj) Aj
        := by
    change normalizedFluctuation P (1 : Mat d) j j 0 a = _
    rw [normalizedFluctuation, hcell]
  rw [hSelfEq]
  set Cb := coarseBlock (HighContrast.adaptedCell (1 : Mat d) j) a with hCbdef
  have hCbSym : IsSymmetricBlockMat Cb := isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1)
  have hCbPosDef : Book.Ch02.BlockPosDef Cb := by
    have h0 := Annealed.blockPosDef_coarseBlock_adapted (1 : Mat d) (Geometry.isUnit_one_grid d)
      j 0 a
    rwa [hcell] at h0
  have hCbFullPosDef : (toFullBlockMat Cb).PosDef :=
    posDef_toFullBlockMat hCbSym hCbPosDef
  have hIdentity : toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
    ext (i|i) (j|j) <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hScale : ∀ (c : ℝ) (A : BlockMat d),
      toFullBlockMat (blockScale c A) = c • toFullBlockMat A := by
    intro c A; ext (i|i) (j|j) <;> rfl
  have hSubFull : ∀ (A B : BlockMat d),
      toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
    intro A B; ext (i|i) (j|j) <;> rfl
  have hHermScale : ∀ (c : ℝ) (A : BlockMat d), (toFullBlockMat A).IsHermitian →
      (toFullBlockMat (blockScale c A)).IsHermitian := by
    intro c A hA
    rw [hScale]
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.eq, star_trivial]
  have hAjHerm := hAjPosDef.isHermitian
  have hEHerm := hEPosDef.isHermitian
  have hCbHerm := hCbFullPosDef.isHermitian
  have hREHerm := hREPosDef.isHermitian
  have hIherm : (toFullBlockMat (Book.Ch02.blockIdentity d)).IsHermitian := by
    rw [hIdentity]; exact Matrix.isHermitian_one
  have hRE_le_Ajf : toFullBlockMat RE ≤ (2 : ℝ) • toFullBlockMat Aj := by
    have h1 := (Annealed.fullBlock_le_iff (hHermScale (1/2) RE hREHerm) hAjHerm).2 hRE_le_Aj
    rw [hScale] at h1
    have h2 := smul_le_smul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
    rwa [smul_smul, show (2:ℝ) * (1/2) = 1 by norm_num, one_smul] at h2
  have hAj_le_E2f : toFullBlockMat Aj ≤ (2 : ℝ) • toFullBlockMat E := by
    have h1 := (Annealed.fullBlock_le_iff hAjHerm (hHermScale 2 E hEHerm)).2 hAj_le_E2
    rwa [hScale] at h1
  have hE_le_6REf : toFullBlockMat E ≤ (6 * aspectRatio E) • toFullBlockMat RE := by
    have h1 := (Annealed.fullBlock_le_iff hEHerm
      (hHermScale (6 * aspectRatio E) RE hREHerm)).2 hE6RE_block
    rwa [hScale] at h1
  have hE_le_12Ajf : toFullBlockMat E ≤ (12 * aspectRatio E) • toFullBlockMat Aj := by
    calc toFullBlockMat E ≤ (6 * aspectRatio E) • toFullBlockMat RE := hE_le_6REf
      _ ≤ (6 * aspectRatio E) • ((2:ℝ) • toFullBlockMat Aj) :=
          smul_le_smul_of_nonneg_left hRE_le_Ajf (by positivity)
      _ = (12 * aspectRatio E) • toFullBlockMat Aj := by
          rw [smul_smul]; ring_nf
  have hXE_full : toFullBlockMat Cb ≤ X • toFullBlockMat E := by
    have h1 := (Annealed.fullBlock_le_iff hCbHerm (hHermScale X E hEHerm)).2 hXE
    rwa [hScale] at h1
  have hCb_le_12PiXAjf : toFullBlockMat Cb ≤ (12 * aspectRatio E * X) • toFullBlockMat Aj := by
    calc toFullBlockMat Cb ≤ X • toFullBlockMat E := hXE_full
      _ ≤ X • ((12 * aspectRatio E) • toFullBlockMat Aj) :=
          smul_le_smul_of_nonneg_left hE_le_12Ajf hX
      _ = (12 * aspectRatio E * X) • toFullBlockMat Aj := by
          rw [smul_smul]; ring_nf
  have hAjf_nonneg : (0 : FullBlockMat d) ≤ toFullBlockMat Aj :=
    Matrix.nonneg_iff_posSemidef.mpr hAjPosDef.posSemidef
  have hCbf_nonneg : (0 : FullBlockMat d) ≤ toFullBlockMat Cb :=
    Matrix.nonneg_iff_posSemidef.mpr hCbFullPosDef.posSemidef
  have hDiff_le : toFullBlockMat Cb - toFullBlockMat Aj ≤
      (12 * aspectRatio E * X) • toFullBlockMat Aj :=
    (sub_le_self _ hAjf_nonneg).trans hCb_le_12PiXAjf
  have hDiff_ge : -(toFullBlockMat Aj) ≤ toFullBlockMat Cb - toFullBlockMat Aj := by
    have h := add_le_add_right hCbf_nonneg (-(toFullBlockMat Aj))
    simpa [sub_eq_add_neg] using h
  set S := matSqrt (toFullBlockMat Aj)⁻¹ with hSdef
  have hSPosDef : S.PosDef := Multiscale.matSqrt_inv_posDef_full hAjPosDef
  have hSHerm : S.IsHermitian := hSPosDef.isHermitian
  have hSelfId : S * toFullBlockMat Aj * S = 1 :=
    matSqrt_inv_conj hAjPosDef
  have hCongr : ∀ {A B : FullBlockMat d}, A ≤ B → S * A * S ≤ S * B * S := by
    intro A B h
    apply Matrix.le_iff.mpr
    have heq : S * B * S - S * A * S = S * (B - A) * S := by
      rw [mul_sub, sub_mul]
    rw [heq]
    have hp := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same S
    rwa [hSHerm.eq] at hp
  have hLowerCongr := hCongr hDiff_ge
  have hUpperCongr := hCongr hDiff_le
  have hLneg : S * (-(toFullBlockMat Aj)) * S = -1 := by
    have heq : S * (-(toFullBlockMat Aj)) * S = -(S * toFullBlockMat Aj * S) := by
      rw [mul_neg, neg_mul]
    rw [heq, hSelfId]
  have hUscale : S * ((12 * aspectRatio E * X) • toFullBlockMat Aj) * S =
      (12 * aspectRatio E * X) • (1 : FullBlockMat d) := by
    have heq : S * ((12 * aspectRatio E * X) • toFullBlockMat Aj) * S =
        (12 * aspectRatio E * X) • (S * toFullBlockMat Aj * S) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [heq, hSelfId]
  rw [hLneg] at hLowerCongr
  rw [hUscale] at hUpperCongr
  have hNormEq : toFullBlockMat (normalizedBlock (blockSub Cb Aj) Aj) =
      S * (toFullBlockMat Cb - toFullBlockMat Aj) * S := by
    change toFullBlockMat (ofFullBlockMat (matSqrt (toFullBlockMat Aj)⁻¹ *
      toFullBlockMat (blockSub Cb Aj) * matSqrt (toFullBlockMat Aj)⁻¹)) = _
    rw [toFullBlockMat_ofFullBlockMat, hSubFull]
  rw [← hNormEq] at hLowerCongr hUpperCongr
  have hDiffHerm : (toFullBlockMat Cb - toFullBlockMat Aj).IsHermitian := hCbHerm.sub hAjHerm
  have hNormHerm : (toFullBlockMat (normalizedBlock (blockSub Cb Aj) Aj)).IsHermitian := by
    rw [hNormEq]
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hSHerm.eq, hDiffHerm.eq, mul_assoc]
  have hHermNegI : (toFullBlockMat (blockScale (-1) (Book.Ch02.blockIdentity d))).IsHermitian :=
    hHermScale (-1) (Book.Ch02.blockIdentity d) hIherm
  have hHermScaleI : (toFullBlockMat
      (blockScale (12 * aspectRatio E * X) (Book.Ch02.blockIdentity d))).IsHermitian :=
    hHermScale (12 * aspectRatio E * X) (Book.Ch02.blockIdentity d) hIherm
  refine ⟨?_, ?_⟩
  · apply (Annealed.fullBlock_le_iff hHermNegI hNormHerm).mp
    rw [hScale, hIdentity]
    simpa [neg_one_smul] using hLowerCongr
  · apply (Annealed.fullBlock_le_iff hNormHerm hHermScaleI).mp
    rw [hScale, hIdentity]
    exact hUpperCongr

/-- B5 (kernel). `e.initial.source.bounds`, second half: `E|V^Id_j|^Q_{S_Q} ≤ (CΠ)^Q`. -/
theorem normalizedFluctuationSelf_one_moment_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ j : ℤ, (jStar : ℤ) ≤ j →
            (∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P (1 : Mat d) j a) ^ bigQ d γ ∂P) ≤
              2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ bigQ d γ) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc1, hCsrc1_pos, hSand⟩ := normalizedFluctuationSelf_one_sandwich d hd γ hγ
  obtain ⟨Csrc2, hCsrc2_pos, hEnv⟩ := coarseBlock_one_source_envelope d hd γ hγ
  refine ⟨max Csrc1 Csrc2, lt_max_of_lt_left hCsrc1_pos, ?_⟩
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar hCthresh j hj
  have : IsProbabilityMeasure P := hP
  have hK1 : (1 : ℝ) < K := hdag.one_lt_growthWitness
  have hCthresh1 : ⌈Csrc1 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK1 Csrc1 (max Csrc1 Csrc2) (le_max_left _ _) jStar hCthresh
  have hCthresh2 : ⌈Csrc2 * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    ceil_source_threshold_le_of_le K hK1 Csrc2 (max Csrc1 Csrc2) (le_max_right _ _) jStar hCthresh
  obtain ⟨X, hXmeas, hXnonneg, hXint, hXmom, hXenv⟩ :=
    hEnv P E Ψ K Src hP hstat hunit hdag jStar hjStar hCthresh2 j hj
  set Q := bigQ d γ with hQdef
  have hQ2 : 2 ≤ Q := bigQ_two_le d γ hγ
  have hQ1 : 1 ≤ Q := by omega
  have hQreal1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hPi1 : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hPi0 : (0 : ℝ) ≤ aspectRatio E := zero_le_one.trans hPi1
  have hIdentity : toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
    ext (i|i) (k|k) <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hScale : ∀ (c : ℝ) (A : BlockMat d),
      toFullBlockMat (blockScale c A) = c • toFullBlockMat A := by
    intro c A; ext (i|i) (k|k) <;> rfl
  have hHermScale : ∀ (c : ℝ) (A : BlockMat d), (toFullBlockMat A).IsHermitian →
      (toFullBlockMat (blockScale c A)).IsHermitian := by
    intro c A hA
    rw [hScale]
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.eq, star_trivial]
  have hIherm : (toFullBlockMat (Book.Ch02.blockIdentity d)).IsHermitian := by
    rw [hIdentity]; exact Matrix.isHermitian_one
  have hScaleIMono : ∀ {c1 c2 : ℝ}, c1 ≤ c2 →
      BlockMatLoewnerLE (blockScale c1 (Book.Ch02.blockIdentity d))
        (blockScale c2 (Book.Ch02.blockIdentity d)) := by
    intro c1 c2 hc
    apply (Annealed.fullBlock_le_iff (hHermScale c1 _ hIherm) (hHermScale c2 _ hIherm)).mp
    rw [hScale, hScale, hIdentity]
    apply Matrix.le_iff.mpr
    have heq : c2 • (1 : FullBlockMat d) - c1 • (1 : FullBlockMat d) =
        (c2 - c1) • (1 : FullBlockMat d) := by
      rw [← sub_smul]
    rw [heq]
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hc)
  have hSymAE : ∀ᵐ a ∂P, IsSymmetricBlockMat (normalizedFluctuationSelf P (1 : Mat d) j a) := by
    have hmem := Annealed.memLqSchatten_normalizedFluctuation d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : Mat d) (Geometry.one_posDef d) j j 0 (Q : ℝ) hQreal1
    rw [Geometry.explicitRoundedGrid_one] at hmem
    exact hmem.symmetric
  have hBoundAE : ∀ᵐ a ∂P, absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P (1 : Mat d) j a)
    ^ Q ≤
      2 * (d : ℝ) * (1 + (12 * aspectRatio E * X a) ^ Q) := by
    filter_upwards [hXenv, hSymAE] with a ha hsym
    obtain ⟨hlo, hhi⟩ := hSand P E Ψ K Src hP hstat hunit hdag jStar hjStar hCthresh1 j hj
      a (X a) (hXnonneg a) ha
    have ht0 : 0 ≤ 12 * aspectRatio E * X a :=
      mul_nonneg (by linarith only [hPi0]) (hXnonneg a)
    have hhi' : BlockMatLoewnerLE (normalizedFluctuationSelf P (1 : Mat d) j a)
        (blockScale (max 1 (12 * aspectRatio E * X a)) (Book.Ch02.blockIdentity d)) :=
      hhi.trans (hScaleIMono (le_max_right 1 (12 * aspectRatio E * X a)))
    have hsandwich := absSchattenNorm_pow_le_of_sandwich Q hQ1
      (normalizedFluctuationSelf P (1 : Mat d) j a) hsym
      (max 1 (12 * aspectRatio E * X a)) (le_max_left 1 _) hlo hhi'
    have hmaxpow : (max 1 (12 * aspectRatio E * X a)) ^ Q ≤ 1 + (12 * aspectRatio E * X a) ^ Q := by
      rcases le_or_gt (12 * aspectRatio E * X a) 1 with h1 | h1
      · rw [max_eq_left h1, one_pow]
        have hpow0 : (0 : ℝ) ≤ (12 * aspectRatio E * X a) ^ Q := pow_nonneg ht0 Q
        linarith only [hpow0]
      · rw [max_eq_right h1.le]
        linarith only []
    calc absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P (1 : Mat d) j a) ^ Q
        ≤ 2 * (d : ℝ) * (max 1 (12 * aspectRatio E * X a)) ^ Q := hsandwich
      _ ≤ 2 * (d : ℝ) * (1 + (12 * aspectRatio E * X a) ^ Q) :=
          mul_le_mul_of_nonneg_left hmaxpow (by positivity)
  have hLHSnonneg : ∀ᵐ a ∂P,
      0 ≤ absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P (1 : Mat d) j a) ^ Q := by
    filter_upwards [hSymAE] with a hsym
    exact pow_nonneg (Analysis.absSchattenNorm_nonneg
      ((Analysis.toFullBlockMat_isHermitian_iff _).2 hsym) hQreal1) Q
  have hXpowInt : Integrable (fun a => (12 * aspectRatio E * X a) ^ Q) P := by
    have heq : (fun a => (12 * aspectRatio E * X a) ^ Q) =
        (fun a => (12 * aspectRatio E) ^ Q * (X a) ^ Q) := by
      funext a; rw [mul_pow]
    rw [heq]
    exact hXint.const_mul _
  have hRHSint : Integrable
      (fun a => 2 * (d : ℝ) * (1 + (12 * aspectRatio E * X a) ^ Q)) P :=
    ((integrable_const (1 : ℝ)).add hXpowInt).const_mul (2 * (d : ℝ))
  have hIntLe := MeasureTheory.integral_mono_of_nonneg hLHSnonneg hRHSint hBoundAE
  have hstep1 : (∫ a, 2 * (d : ℝ) * (1 + (12 * aspectRatio E * X a) ^ Q) ∂P) =
      2 * (d : ℝ) * (1 + (12 * aspectRatio E) ^ Q * ∫ a, (X a) ^ Q ∂P) := by
    rw [integral_const_mul]
    congr 1
    have hintegrand_eq : (fun a => (1 : ℝ) + (12 * aspectRatio E * X a) ^ Q) =
        (fun a => (1 : ℝ) + (12 * aspectRatio E) ^ Q * (X a) ^ Q) := by
      funext a; rw [mul_pow]
    rw [hintegrand_eq, integral_add (integrable_const (1 : ℝ)) (hXint.const_mul _),
      integral_const, integral_const_mul, probReal_univ, one_smul]
  have h12Pi0 : (0 : ℝ) ≤ 12 * aspectRatio E := by positivity
  have hbound : (1 : ℝ) + (12 * aspectRatio E) ^ Q * (∫ a, (X a) ^ Q ∂P) ≤
      1 + (12 * aspectRatio E) ^ Q * (2 : ℝ) ^ Q := by
    have hmul := mul_le_mul_of_nonneg_left hXmom (pow_nonneg h12Pi0 Q)
    linarith only [hmul]
  have hRHSchain :
      (∫ a, 2 * (d : ℝ) * (1 + (12 * aspectRatio E * X a) ^ Q) ∂P) ≤
        2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q) := by
    rw [hstep1]
    calc 2 * (d : ℝ) * (1 + (12 * aspectRatio E) ^ Q * (∫ a, (X a) ^ Q ∂P))
        ≤ 2 * (d : ℝ) * (1 + (12 * aspectRatio E) ^ Q * (2 : ℝ) ^ Q) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 2 * (d : ℝ) * (1 + (24 * aspectRatio E) ^ Q) := by
          have hbase : (12 * aspectRatio E) ^ Q * (2 : ℝ) ^ Q = (24 * aspectRatio E) ^ Q := by
            rw [← mul_pow]; congr 1; ring
          rw [hbase]
  exact hIntLe.trans hRHSchain

/-- B6 (kernel). The seed: the Euclidean fluctuation history at `j_*` is the single-cell
moment (`adaptedLatticeAtScale 1 j_* ∩ adaptedCell 1 j_* = {0}`, both cells open). -/
theorem fluctuationHistory_one_jStar_le_moment (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (Src : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K Src →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        fluctuationHistory P γ (1 : Mat d) jStar (jStar : ℤ) ≤
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
            (normalizedFluctuationSelf P (1 : Mat d) (jStar : ℤ) a) ^ bigQ d γ ∂P := by
  intro P E Ψ K Src hP hstat hunit hdag jStar hjStar
  have : IsProbabilityMeasure P := hP
  let : NeZero d := ⟨by omega⟩
  set Q := bigQ d γ with hQdef
  have hQ2 : 2 ≤ Q := bigQ_two_le d γ hγ
  have hQ1 : 1 ≤ Q := by omega
  have hQreal1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hcellEq : HighContrast.adaptedCell (1 : Mat d) (jStar : ℤ) =
      HighContrast.centeredCube d (jStar : ℤ) := by
    rw [Geometry.adaptedCell_one, ← Geometry.centeredCube_eq_standardCell]
  -- Every point of the intersecting lattice/cell set is the origin.
  have hSet_sub : ∀ z : Vec d,
      z ∈ adaptedLatticeAtScale (1 : Mat d) (jStar : ℤ) ∩ HighContrast.adaptedCell (1 : Mat d)
        (jStar : ℤ) →
      z = 0 := by
    rintro z ⟨⟨w, hw⟩, hzmem⟩
    rw [hcellEq, Recurrence.mem_centeredCube_iff] at hzmem
    have hw0 : w = 0 := by
      funext i
      change w i = (0 : ℤ)
      have hzi : z i = (3 : ℝ) ^ (jStar : ℤ) * (w i : ℝ) := by
        rw [← hw]
        simp [adaptedCellCenter, Geometry.matVecMul_eq_mulVec, Matrix.one_mulVec]
      have hb := hzmem i
      rw [hzi] at hb
      obtain ⟨hb1, hb2⟩ := hb
      have hpow : (0 : ℝ) < (3 : ℝ) ^ (jStar : ℤ) := by positivity
      have h1' : (3 : ℝ) ^ (jStar : ℤ) * (-(1 / 2 : ℝ)) < (3 : ℝ) ^ (jStar : ℤ) * (w i : ℝ) := by
        rw [mul_comm ((3 : ℝ) ^ (jStar : ℤ)) (-(1 / 2 : ℝ))]; exact hb1
      have h2' : (3 : ℝ) ^ (jStar : ℤ) * (w i : ℝ) < (3 : ℝ) ^ (jStar : ℤ) * (1 / 2 : ℝ) := by
        rw [mul_comm (1 / 2 : ℝ) ((3 : ℝ) ^ (jStar : ℤ))] at hb2; exact hb2
      have hlt1 : (-(1 / 2 : ℝ)) < (w i : ℝ) := lt_of_mul_lt_mul_left h1' hpow.le
      have hlt2 : (w i : ℝ) < (1 / 2 : ℝ) := lt_of_mul_lt_mul_left h2' hpow.le
      have hlt1' : (-1 : ℤ) < 2 * w i := by
        have hcast : ((-1 : ℤ) : ℝ) < ((2 * w i : ℤ) : ℝ) := by push_cast; linarith only [hlt1]
        exact_mod_cast hcast
      have hlt2' : 2 * w i < (1 : ℤ) := by
        have hcast : ((2 * w i : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith only [hlt2]
        exact_mod_cast hcast
      omega
    rw [← hw, hw0]
    funext i
    simp [adaptedCellCenter, Geometry.matVecMul_eq_mulVec, Matrix.one_mulVec]
  -- Generic collapse of a real supremum over a proposition-indexed family.
  have hCollapse : ∀ {p : Prop} (f : p → ℝ) (a0 : ℝ),
      (∀ h : p, f h ≤ a0) → (¬ p → (0 : ℝ) ≤ a0) → (⨆ h : p, f h) ≤ a0 := by
    intro p f a0 hpos hneg
    by_cases hp : p
    · rw [ciSup_pos hp]; exact hpos hp
    · have : IsEmpty p := ⟨hp⟩
      rw [Real.iSup_of_isEmpty]
      exact hneg hp
  have hSymAE : ∀ᵐ a ∂P, IsSymmetricBlockMat (normalizedFluctuationSelf P (1 : Mat d) (jStar :
    ℤ) a) := by
    have hmem := Annealed.memLqSchatten_normalizedFluctuation d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : Mat d) (Geometry.one_posDef d) (jStar : ℤ) (jStar : ℤ) 0 (Q : ℝ) hQreal1
    rw [Geometry.explicitRoundedGrid_one] at hmem
    exact hmem.symmetric
  have hRHSint : Integrable
      (fun a => absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P (1 : Mat d) (jStar : ℤ) a)
        ^ Q) P := by
    have hmem := Annealed.memLqSchatten_normalizedFluctuation d hd P γ E Ψ K Src hstat hdag
      jStar hjStar (1 : Mat d) (Geometry.one_posDef d) (jStar : ℤ) (jStar : ℤ) 0 (Q : ℝ) hQreal1
    rw [Geometry.explicitRoundedGrid_one] at hmem
    have hint := hmem.integrable
    simpa [Real.rpow_natCast] using! hint
  have hLHSnonneg : ∀ᵐ a ∂P, (0 : ℝ) ≤
      ⨆ jj ∈ Set.Icc (jStar : ℤ) (jStar : ℤ),
        (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((jStar : ℝ) - (jj : ℝ))) *
          ⨆ z ∈ adaptedLatticeAtScale (1 : Mat d) jj ∩ HighContrast.adaptedCell (1 : Mat d)
            (jStar : ℤ),
            blockOpNorm (normalizedFluctuation P (1 : Mat d) jj (jStar : ℤ) z a) ^ Q := by
    apply ae_of_all
    intro a
    apply Real.iSup_nonneg
    intro jj
    apply Real.iSup_nonneg
    intro _hjj
    apply mul_nonneg (by positivity)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact pow_nonneg (norm_nonneg _) Q
  have hBoundAE : ∀ᵐ a ∂P,
      (⨆ jj ∈ Set.Icc (jStar : ℤ) (jStar : ℤ),
        (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((jStar : ℝ) - (jj : ℝ))) *
          ⨆ z ∈ adaptedLatticeAtScale (1 : Mat d) jj ∩ HighContrast.adaptedCell (1 : Mat d)
            (jStar : ℤ),
            blockOpNorm (normalizedFluctuation P (1 : Mat d) jj (jStar : ℤ) z a) ^ Q) ≤
        absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P (1 : Mat d) (jStar : ℤ) a) ^ Q := by
    filter_upwards [hSymAE] with a hsym
    have hHerm : (toFullBlockMat (normalizedFluctuationSelf P (1 : Mat d) (jStar : ℤ)
      a)).IsHermitian :=
      (Analysis.toFullBlockMat_isHermitian_iff _).2 hsym
    have htarget_nonneg : (0 : ℝ) ≤
        absSchattenNorm (Q : ℝ) (normalizedFluctuationSelf P (1 : Mat d) (jStar : ℤ) a) ^ Q :=
      pow_nonneg (Analysis.absSchattenNorm_nonneg hHerm hQreal1) Q
    apply ciSup_le
    intro jj
    apply hCollapse
    · intro hjjIcc
      have hjjeq : jj = (jStar : ℤ) :=
        le_antisymm (Set.mem_Icc.mp hjjIcc).2 (Set.mem_Icc.mp hjjIcc).1
      subst hjjeq
      push_cast
      have hweight : (3 : ℝ) ^ (-(Q : ℝ) * rhoMax d γ * ((jStar : ℝ) - (jStar : ℝ))) = 1 := by
        simp
      rw [hweight, one_mul]
      apply ciSup_le
      intro z
      apply hCollapse
      · intro hzmem
        have hz0 : z = 0 := hSet_sub z hzmem
        subst hz0
        change blockOpNorm (normalizedFluctuationSelf P (1 : Mat d) (jStar : ℤ) a) ^ Q ≤ _
        exact pow_le_pow_left₀ (norm_nonneg _)
          (Analysis.blockOpNorm_le_absSchattenNorm hHerm hQreal1) Q
      · intro _; exact htarget_nonneg
    · intro _; exact htarget_nonneg
  unfold fluctuationHistory
  exact MeasureTheory.integral_mono_of_nonneg hLHSnonneg hRHSint hBoundAE

end

end HCPolySupport.HighContrast.Multiscale

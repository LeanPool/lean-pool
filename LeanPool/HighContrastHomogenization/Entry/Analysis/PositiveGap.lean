/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGapSupport

/-!
# High-contrast homogenization: Entry.Analysis.PositiveGap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# PositiveGap random-field assembly

This module assembles the ordered random difference and the deterministic mean-gap
receipts that the positive-gap estimates consume, and proves the nonlinear, Young
absorption and centered forms of the positive-gap estimate `l.fixed.geometry.positive.gap`.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub blockTrace)
namespace HCPolySupport.HighContrast.Analysis

open MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

private theorem full_blockSub {d : ℕ} (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

private theorem blockTrace_blockSub {d : ℕ} (A B : BlockMat d) :
    blockTrace (blockSub A B) = blockTrace A - blockTrace B := by
  unfold blockTrace
  rw [full_blockSub]
  exact Matrix.trace_sub (toFullBlockMat A) (toFullBlockMat B)

private theorem zero_mean_eq {d : ℕ} (P : Measure (CoeffSpace d)) :
    ofFullBlockMat (Matrix.of fun α β : BlockCoord d =>
        ∫ _a, blockMatEntry (ofFullBlockMat (0 : FullBlockMat d)) α β ∂P) =
      ofFullBlockMat (0 : FullBlockMat d) := by
  congr 1
  ext α β
  simp

private theorem blockSub_zero {d : ℕ} (A : BlockMat d) :
    blockSub A (ofFullBlockMat (0 : FullBlockMat d)) = A := by
  calc
    blockSub A (ofFullBlockMat (0 : FullBlockMat d)) =
        ofFullBlockMat (toFullBlockMat (blockSub A (ofFullBlockMat 0))) :=
      (ofFullBlockMat_toFullBlockMat _).symm
    _ = ofFullBlockMat (toFullBlockMat A) := by
      congr 1
      rw [full_blockSub]
      ext α β
      simp
    _ = A := ofFullBlockMat_toFullBlockMat A

private theorem blockTrace_le_of_blockLoewnerLE_local {d : ℕ} {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) :
    blockTrace A ≤ blockTrace B := by
  have hdiff : (toFullBlockMat (blockSub B A)).PosSemidef := by
    have horder : toFullBlockMat A ≤ toFullBlockMat B := by
      rw [Matrix.le_iff]
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA.isHermitian) ?_
      intro q
      let X : BlockVec d := ofFullBlockVec q
      have hquad :
          dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q) =
            blockVecDot X
              (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) := by
        rw [← dotProduct_toFullBlockVec X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X)]
        rw [toFullBlockVec_blockMatVecMul]
        simp [X]
      have hdiffq :
          blockVecDot X
              (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
            blockVecDot X (blockMatVecMul B X) -
              blockVecDot X (blockMatVecMul A X) := by
        simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
      have hle := hAB X
      change 0 ≤ dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q)
      rw [hquad, hdiffq]
      linarith only [hle]
    rw [full_blockSub]
    exact (Matrix.le_iff).mp horder
  have htr := blockTrace_nonneg hdiff
  rw [blockTrace_blockSub B A] at htr
  linarith only [htr]

/-- The ordered difference `D = G - F` and its entrywise mean receipts. -/
theorem positiveGap_ordered_data {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {N : ℝ} (hN : 1 ≤ N)
    {F G : CoeffSpace d → BlockMat d}
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G)
    (hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a))
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    let D : CoeffSpace d → BlockMat d := fun a => blockSub (G a) (F a)
    let MF : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
    let MG : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    SchattenMemLp P N D ∧
      (∀ᵐ a ∂P, (toFullBlockMat (D a)).PosSemidef ∧
        BlockMatLoewnerLE (D a) (G a)) ∧
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (D a) α β ∂P) =
        blockSub MG MF ∧
      (toFullBlockMat MF).PosSemidef ∧
      (toFullBlockMat MG).PosSemidef ∧
      (toFullBlockMat (blockSub MG MF)).PosSemidef ∧
      BlockMatLoewnerLE (blockSub MG MF) MG := by
  dsimp
  let D : CoeffSpace d → BlockMat d := fun a => blockSub (G a) (F a)
  let MF : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
  let MG : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
  have hD : SchattenMemLp P N D := hG.sub hF hN
  have hFint : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (F a) α β) P :=
    fun α β => hF.integrable_entry hN α β
  have hGint : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (G a) α β) P :=
    fun α β => hG.integrable_entry hN α β
  have hDae :
      ∀ᵐ a ∂P, (toFullBlockMat (D a)).PosSemidef ∧ BlockMatLoewnerLE (D a) (G a) := by
    filter_upwards [hF.symmetric, hG.symmetric, hFpos, hFG] with a hFs hGs hFp hFo
    have hgap := ordered_gap_posSemidef hFs hGs hFp hFo
    exact ⟨hgap.1, hgap.2.2⟩
  have hED : ofFullBlockMat
        (Matrix.of fun α β => ∫ a, blockMatEntry (D a) α β ∂P) =
      blockSub MG MF := by
    simpa [D, MF, MG] using integral_blockSub (P := P) (F := G) (G := F) hGint hFint
  have hMFsym : IsSymmetricBlockMat MF := by
    simpa [MF] using isSymmetricBlockMat_integral (P := P) (H := F) hF.symmetric
  have hMGsym : IsSymmetricBlockMat MG := by
    simpa [MG] using isSymmetricBlockMat_integral (P := P) (H := G) hG.symmetric
  have h0int :
      ∀ α β : BlockCoord d,
        Integrable (fun _a : CoeffSpace d =>
          blockMatEntry (ofFullBlockMat (0 : FullBlockMat d)) α β) P :=
    fun _ _ => integrable_const _
  have hMFpos_order : BlockMatLoewnerLE (ofFullBlockMat 0) MF := by
    have hraw := blockMatLoewnerLE_integral (P := P)
      (F := fun _a : CoeffSpace d => ofFullBlockMat (0 : FullBlockMat d))
      (G := F) h0int hFint hFpos
    simpa [MF, zero_mean_eq P] using! hraw
  have hMFG : BlockMatLoewnerLE MF MG := by
    simpa [MF, MG] using blockMatLoewnerLE_integral (P := P) (F := F) (G := G)
      hFint hGint hFG
  obtain ⟨hMeanGap, hMGpos, hMeanOrder⟩ :=
    ordered_gap_posSemidef hMFsym hMGsym hMFpos_order hMFG
  have hMFpsd : (toFullBlockMat MF).PosSemidef := by
    have hzeroSym : IsSymmetricBlockMat (ofFullBlockMat (0 : FullBlockMat d)) := by
      intro α β
      simp
    have hzeroOrder : BlockMatLoewnerLE
        (ofFullBlockMat (0 : FullBlockMat d)) (ofFullBlockMat 0) := by
      intro X
      exact le_rfl
    have hgap0 := ordered_gap_posSemidef hzeroSym hMFsym hzeroOrder hMFpos_order
    simpa [blockSub_zero] using hgap0.1
  exact ⟨hD, hDae, hED, hMFpsd, hMGpos, by simpa [hED] using hMeanGap,
    by simpa [hED] using hMeanOrder⟩

/-- Deterministic mean-gap bounds used in the centering step. -/
theorem positiveGap_mean_gap_bounds {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {N : ℝ} (hN : 1 ≤ N)
    {F G : CoeffSpace d → BlockMat d}
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G)
    (hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a))
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    let MF : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
    let MG : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    0 ≤ blockTrace (blockSub MG MF) ∧
      absSchattenNorm N (blockSub MG MF) ≤ blockTrace (blockSub MG MF) ∧
      blockTrace (blockSub MG MF) ≤ (2 * (d : ℝ)) * blockOpNorm MG ∧
      blockTrace (blockSub MG MF) ≤
        (2 * (d : ℝ)) ^ (1 - N⁻¹) * blockOpNorm MG ^ (1 - N⁻¹) *
          blockTrace (blockSub MG MF) ^ N⁻¹ := by
  dsimp
  let MF : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
  let MG : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
  have hdata := positiveGap_ordered_data (P := P) hN hF hG hFpos hFG
  dsimp only at hdata
  rcases hdata with ⟨_hD, _hDae, _hED, _hMFpos, hMGpos, hGap, hGapLE⟩
  have hGapTrace : 0 ≤ blockTrace (blockSub MG MF) := blockTrace_nonneg hGap
  refine ⟨hGapTrace, absSchattenNorm_le_blockTrace hGap hN, ?_, ?_⟩
  · exact (blockTrace_le_of_blockLoewnerLE_local hGap hMGpos.isHermitian hGapLE).trans
      (blockTrace_le_dim_mul_blockOpNorm hMGpos)
  · exact ordered_trace_le_dim_rpow_mul_opNorm_rpow_mul_trace_rpow hGap hMGpos.isHermitian
      hGapLE hN

private theorem scalar_root_multiple_memLp_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N k : ℝ} (hN : 0 < N) (hk : 0 ≤ k)
    {t : α → ℝ} (ht : 0 ≤ᵐ[μ] t) (hint : Integrable t μ) :
    MemLp (fun a => k * t a ^ N⁻¹) (ENNReal.ofReal N) μ ∧
      (eLpNorm (fun a => k * t a ^ N⁻¹) (ENNReal.ofReal N) μ).toReal =
        k * (∫ a, t a ∂μ) ^ N⁻¹ := by
  have hu : 0 ≤ᵐ[μ] fun a => k * t a ^ N⁻¹ :=
    ht.mono fun a ha => mul_nonneg hk (Real.rpow_nonneg ha _)
  have hpow : (fun a => (k * t a ^ N⁻¹) ^ N) =ᵐ[μ] fun a => k ^ N * t a := by
    filter_upwards [ht] with a ha
    rw [Real.mul_rpow hk (Real.rpow_nonneg ha _), Real.rpow_inv_rpow ha hN.ne']
  have hmeas : AEStronglyMeasurable (fun a => k * t a ^ N⁻¹) μ :=
    ((hint.aestronglyMeasurable.aemeasurable.pow_const N⁻¹).aestronglyMeasurable).const_mul k
  have hmem : MemLp (fun a => k * t a ^ N⁻¹) (ENNReal.ofReal N) μ := by
    rw [← integrable_norm_rpow_iff hmeas
      (ne_of_gt (ENNReal.ofReal_pos.mpr hN)) ENNReal.ofReal_ne_top]
    apply (hint.const_mul (k ^ N)).congr
    filter_upwards [hu, hpow] with a ha he
    simpa only [ENNReal.toReal_ofReal hN.le, Real.norm_of_nonneg ha] using he.symm
  refine ⟨hmem, ?_⟩
  rw [scalar_eLpNorm_toReal_eq_root hN hu hmem, integral_congr_ae hpow,
    integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hk _) (integral_nonneg_of_ae ht),
    Real.rpow_rpow_inv hk hN.ne']

/-- `l.fixed.geometry.positive.gap`: the nonlinear inequality, with genuine scalar moments and
finite real norm readbacks. The Hölder inputs are the centered majorant and gap
Schatten functions, with conjugate exponents `N/(N-1)` and `N`. -/
theorem positiveGap_nonlinear {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {N : ℝ} (hN : 1 < N)
    {F G : CoeffSpace d → BlockMat d}
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G)
    (hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a))
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    let MF : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
    let MG : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    lqSchattenNorm P N (fun a => blockSub (G a) (F a)) ≤
      blockOpNorm MG ^ (1 - N⁻¹) * blockTrace (blockSub MG MF) ^ N⁻¹ +
        (2 * (d : ℝ)) ^ ((N - 1) / N ^ 2) *
          lqSchattenNorm P N (fun a => blockSub (G a) MG) ^ (1 - N⁻¹) *
          lqSchattenNorm P N (fun a => blockSub (G a) (F a)) ^ N⁻¹ := by
  dsimp only
  let D : CoeffSpace d → BlockMat d := fun a => blockSub (G a) (F a)
  let MF : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
  let MG : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
  let C : CoeffSpace d → BlockMat d := fun a => blockSub (G a) MG
  let c := blockOpNorm MG
  let m := 2 * (d : ℝ)
  let t : CoeffSpace d → ℝ := fun a => blockTrace (D a)
  let s : CoeffSpace d → ℝ := fun a => absSchattenNorm N (C a)
  let z : CoeffSpace d → ℝ := fun a => absSchattenNorm N (D a)
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hp : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  have hr : 0 ≤ 1 - N⁻¹ := sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hN).le
  have hc : 0 ≤ c := norm_nonneg _
  have hm : 0 ≤ m := by positivity
  have he : (N - 1) * N⁻¹ = 1 - N⁻¹ := by field_simp
  have he' : (1 - N⁻¹) * N⁻¹ = (N - 1) / N ^ 2 := by field_simp
  have hdata := positiveGap_ordered_data hN.le hF hG hFpos hFG
  rcases hdata with ⟨hD, hDae, hED, _hMF, _hMG, _hMD, _hMDG⟩
  have hC : SchattenMemLp P N C := hG.center hN.le
  have hs := hC.memLp_absSchattenNorm hN.le
  have hz := hD.memLp_absSchattenNorm hN.le
  have hsn : 0 ≤ᵐ[P] s := by
    filter_upwards [hC.symmetric] with a ha
    exact absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hN.le
  have hzn : 0 ≤ᵐ[P] z := by
    filter_upwards [hD.symmetric] with a ha
    exact absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hN.le
  have htn : 0 ≤ᵐ[P] t := hDae.mono fun a ha => blockTrace_nonneg ha.1
  have htrace := blockTrace_integral (hD.integrable_entry hN.le)
  have htint : Integrable t P := htrace.1
  have hEt : (∫ a, t a ∂P) = blockTrace (blockSub MG MF) := by
    rw [← htrace.2, hED]
  have hmix := (scalar_holder_power_integrable_bound hN hsn hzn hs hz).1
  have hmixn : 0 ≤ᵐ[P] fun a => s a ^ (N - 1) * z a := by
    filter_upwards [hsn, hzn] with a ha hb
    exact mul_nonneg (Real.rpow_nonneg ha _) hb
  let u : CoeffSpace d → ℝ := fun a => c ^ (1 - N⁻¹) * t a ^ N⁻¹
  let v : CoeffSpace d → ℝ := fun a =>
    m ^ ((N - 1) / N ^ 2) * (s a ^ (N - 1) * z a) ^ N⁻¹
  have hu := scalar_root_multiple_memLp_norm hNpos
    (Real.rpow_nonneg hc (1 - N⁻¹)) htn htint
  have hv := scalar_root_multiple_memLp_norm hNpos
    (Real.rpow_nonneg hm ((N - 1) / N ^ 2)) hmixn hmix
  have hun : 0 ≤ᵐ[P] u := htn.mono fun a ha =>
    mul_nonneg (Real.rpow_nonneg hc _) (Real.rpow_nonneg ha _)
  have hvn : 0 ≤ᵐ[P] v := hmixn.mono fun a ha =>
    mul_nonneg (Real.rpow_nonneg hm _) (Real.rpow_nonneg ha _)
  have hpoint : ∀ᵐ a ∂P, ‖z a‖ ≤ ‖u a + v a‖ := by
    filter_upwards [hDae, hG.symmetric, hC.symmetric, hsn, hzn, htn, hun, hvn]
      with a hDa hGa hCa hsa hza hta hua hva
    rw [Real.norm_of_nonneg hza, Real.norm_of_nonneg (add_nonneg hua hva)]
    have hGH := (toFullBlockMat_isHermitian_iff _).2 hGa
    have hCH := (toFullBlockMat_isHermitian_iff _).2 hCa
    have hop : blockOpNorm (G a) ≤ c + s a := by
      calc
        _ ≤ blockOpNorm (C a) + c := by
          simpa only [blockOpNorm, C, full_blockSub] using!
            norm_le_norm_sub_add (toFullBlockMat (G a)) (toFullBlockMat MG)
        _ ≤ s a + c := add_le_add (blockOpNorm_le_absSchattenNorm hCH hN.le) le_rfl
        _ = c + s a := add_comm _ _
    have htr := trace_le_dim_rpow_mul_absSchattenNorm hDa.1 hN.le
    calc
      z a ≤ blockOpNorm (G a) ^ (1 - N⁻¹) * t a ^ N⁻¹ :=
        absSchattenNorm_gap_le_opNorm_rpow_mul_trace_rpow hDa.1 hGH hDa.2 hN.le
      _ ≤ (c + s a) ^ (1 - N⁻¹) * t a ^ N⁻¹ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) hop hr)
          (Real.rpow_nonneg hta _)
      _ ≤ (c ^ (1 - N⁻¹) + s a ^ (1 - N⁻¹)) * t a ^ N⁻¹ :=
        mul_le_mul_of_nonneg_right (scalar_gap_power_add_le hN.le hc hsa)
          (Real.rpow_nonneg hta _)
      _ = u a + s a ^ (1 - N⁻¹) * t a ^ N⁻¹ := add_mul _ _ _
      _ ≤ u a + s a ^ (1 - N⁻¹) * (m ^ (1 - N⁻¹) * z a) ^ N⁻¹ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hta htr hp)
          (Real.rpow_nonneg hsa _))
      _ = u a + v a := by
        dsimp only [v]
        rw [Real.mul_rpow (Real.rpow_nonneg hm _) hza, ← Real.rpow_mul hm, he',
          Real.mul_rpow (Real.rpow_nonneg hsa _) hza, ← Real.rpow_mul hsa, he]
        ring
  have hsum := scalar_minkowski_toReal hN.le hu.1 hv.1
  have hmono := ENNReal.toReal_mono hsum.1.eLpNorm_ne_top
    (eLpNorm_mono_ae hz.aestronglyMeasurable hpoint)
  have hholder := scalar_mixedMoment_root_le hN hsn hzn hs hz
  have hzr := hD.lqSchattenNorm_eq_eLpNorm_toReal hN.le
  have hsr := hC.lqSchattenNorm_eq_eLpNorm_toReal hN.le
  calc
    lqSchattenNorm P N D = (eLpNorm z (ENNReal.ofReal N) P).toReal := hzr.2.2
    _ ≤ (eLpNorm (fun a => u a + v a) (ENNReal.ofReal N) P).toReal := hmono
    _ ≤ (eLpNorm u (ENNReal.ofReal N) P).toReal +
        (eLpNorm v (ENNReal.ofReal N) P).toReal := hsum.2
    _ = c ^ (1 - N⁻¹) * blockTrace (blockSub MG MF) ^ N⁻¹ +
        m ^ ((N - 1) / N ^ 2) * (∫ a, s a ^ (N - 1) * z a ∂P) ^ N⁻¹ := by
      rw [hu.2, hv.2, hEt]
    _ ≤ c ^ (1 - N⁻¹) * blockTrace (blockSub MG MF) ^ N⁻¹ +
        m ^ ((N - 1) / N ^ 2) *
          ((eLpNorm s (ENNReal.ofReal N) P).toReal ^ (1 - N⁻¹) *
            (eLpNorm z (ENNReal.ofReal N) P).toReal ^ N⁻¹) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hholder (Real.rpow_nonneg hm _))
    _ = _ := by rw [← hsr.2.2, ← hzr.2.2, ← mul_assoc]

/-- `l.fixed.geometry.positive.gap`: Young absorption of the proved nonlinear estimate,
with the printed dimension and rational coefficients. -/
theorem positiveGap_young_absorption {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {N : ℝ} (hN : 1 < N)
    {F G : CoeffSpace d → BlockMat d}
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G)
    (hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a))
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    let MF : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
    let MG : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    lqSchattenNorm P N (fun a => blockSub (G a) (F a)) ≤
      (2 * (d : ℝ)) ^ N⁻¹ *
          lqSchattenNorm P N (fun a => blockSub (G a) MG) +
        N / (N - 1) * blockOpNorm MG ^ (1 - N⁻¹) *
          blockTrace (blockSub MG MF) ^ N⁻¹ := by
  dsimp only
  have hD := (hG.sub hF hN.le).lqSchattenNorm_eq_eLpNorm_toReal hN.le
  have hC := (hG.center hN.le).lqSchattenNorm_eq_eLpNorm_toReal hN.le
  have h := scalar_gap_young_absorb hN (by positivity : 0 ≤ 2 * (d : ℝ))
    hD.2.1 hC.2.1 (positiveGap_nonlinear hN hF hG hFpos hFG)
  simpa only [mul_assoc] using h

/-- Pure block algebra identity behind the centering step. -/
theorem positiveGap_centered_identity {d : ℕ} (F G MF MG : BlockMat d) :
    blockSub F MF =
      blockSub (blockSub G MG) (blockSub (blockSub G F) (blockSub MG MF)) := by
  cases F
  cases G
  cases MF
  cases MG
  simp [blockSub]
  repeat constructor <;> first | abel_nf | trivial

/-- `l.fixed.geometry.positive.gap`: center using two sharp subtraction inequalities,
then bound the deterministic mean gap and insert Young absorption. -/
theorem positiveGap_centered_bound {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {N : ℝ} (hN : 1 < N)
    {F G : CoeffSpace d → BlockMat d}
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G)
    (hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a))
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    let MF : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
    let MG : BlockMat d :=
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    lqSchattenNorm P N (fun a => blockSub (F a) MF) ≤
      (1 + (2 * (d : ℝ)) ^ N⁻¹) *
          lqSchattenNorm P N (fun a => blockSub (G a) MG) +
        (N / (N - 1) + (2 * (d : ℝ)) ^ (1 - N⁻¹)) *
          blockOpNorm MG ^ (1 - N⁻¹) * blockTrace (blockSub MG MF) ^ N⁻¹ := by
  dsimp only
  let MF : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P)
  let MG : BlockMat d :=
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
  let D : CoeffSpace d → BlockMat d := fun a => blockSub (G a) (F a)
  let C : CoeffSpace d → BlockMat d := fun a => blockSub (G a) MG
  let MD := blockSub MG MF
  have hD : SchattenMemLp P N D := hG.sub hF hN.le
  have hC : SchattenMemLp P N C := hG.center hN.le
  have hdata := positiveGap_ordered_data hN.le hF hG hFpos hFG
  have hMD : IsSymmetricBlockMat MD :=
    (toFullBlockMat_isHermitian_iff _).1 hdata.2.2.2.2.2.1.isHermitian
  have hMDmem := memLqSchatten_const P hN.le MD hMD
  have hmean := positiveGap_mean_gap_bounds hN.le hF hG hFpos hFG
  have hyoung := positiveGap_young_absorption hN hF hG hFpos hFG
  calc
    lqSchattenNorm P N (fun a => blockSub (F a) MF) =
        lqSchattenNorm P N (fun a => blockSub (C a) (blockSub (D a) MD)) := by
      congr 1
      funext a
      exact positiveGap_centered_identity (F a) (G a) MF MG
    _ ≤ lqSchattenNorm P N C + lqSchattenNorm P N (fun a => blockSub (D a) MD) :=
      lqSchattenNorm_sub_le hN.le hC (hD.sub hMDmem hN.le)
    _ ≤ lqSchattenNorm P N C +
        (lqSchattenNorm P N D + lqSchattenNorm P N (fun _ => MD)) :=
      add_le_add le_rfl (lqSchattenNorm_sub_le hN.le hD hMDmem)
    _ = lqSchattenNorm P N C + (lqSchattenNorm P N D + absSchattenNorm N MD) := by
      rw [lqSchattenNorm_const P hN.le MD hMD]
    _ ≤ lqSchattenNorm P N C +
        (((2 * (d : ℝ)) ^ N⁻¹ * lqSchattenNorm P N C +
          N / (N - 1) * blockOpNorm MG ^ (1 - N⁻¹) * blockTrace MD ^ N⁻¹) +
          (2 * (d : ℝ)) ^ (1 - N⁻¹) * blockOpNorm MG ^ (1 - N⁻¹) *
            blockTrace MD ^ N⁻¹) :=
      add_le_add le_rfl (add_le_add hyoung (hmean.2.1.trans hmean.2.2.2))
    _ = _ := by ring

end

end HCPolySupport.HighContrast.Analysis

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# High-contrast homogenization: Entry.Analysis.SchattenNormIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schatten Norm Integrability

Integrability and measurability of the Schatten norm of a random matrix, and the membership
predicate the moment estimates are stated with.

It serves `l.fixed.geometry.positive.gap`, whose mixed-norm moment estimate is stated with this
carrier, and `l.fixed.geometry.matrix.averaging`, whose product-integrability bridge uses the
entrywise operator-norm bound.
-/

section
/-!
## Integrability support for the positive-gap estimate

This file collects the supporting lemmas for the positive-gap estimate:
entrywise expectations, trace/order preservation by integration, and basic
membership examples.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub blockTrace
  blockVecDot_blockMatVecMul_eq_sum toFullBlockMat_eq_blockMatEntry)
namespace HCPolySupport.HighContrast

open MeasureTheory
open scoped BigOperators
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

namespace SchattenMemLp

private theorem absSchattenNorm_nonneg_ae {P : Measure (CoeffSpace d)}
    {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : SchattenMemLp P N H) (hN : 1 ≤ N) :
    0 ≤ᵐ[P] fun a => absSchattenNorm N (H a) := by
  filter_upwards [hH.symmetric] with a ha
  exact Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff (H a)).2 ha) hN

private theorem absSchattenNorm_aestronglyMeasurable {P : Measure (CoeffSpace d)}
    {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : SchattenMemLp P N H) (hN : 1 ≤ N) :
    AEStronglyMeasurable (fun a => absSchattenNorm N (H a)) P := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : AEStronglyMeasurable (fun a => absSchattenNorm N (H a) ^ N) P :=
    hH.integrable.aestronglyMeasurable
  have hroot :
      (fun a => (absSchattenNorm N (H a) ^ N) ^ N⁻¹) =ᵐ[P]
        fun a => absSchattenNorm N (H a) := by
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    exact Real.rpow_rpow_inv ha hNpos.ne'
  exact (hpow.aemeasurable.pow_const N⁻¹).aestronglyMeasurable.congr hroot

/-- The real Schatten moment carrier gives the corresponding Mathlib `eLpNorm`
membership of the scalar Schatten norm. -/
theorem memLp_absSchattenNorm {d : ℕ} {P : Measure (CoeffSpace d)}
    {N : ℝ} {H : CoeffSpace d → BlockMat d} (hH : SchattenMemLp P N H) (hN : 1 ≤ N) :
    MemLp (fun a => absSchattenNorm N (H a)) (ENNReal.ofReal N) P := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp0 : ENNReal.ofReal N ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)
  have hsn_meas : AEStronglyMeasurable (fun a => absSchattenNorm N (H a)) P :=
    absSchattenNorm_aestronglyMeasurable hH hN
  rw [← MeasureTheory.integrable_norm_rpow_iff hsn_meas hp0 ENNReal.ofReal_ne_top]
  exact hH.integrable.congr <| by
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    simp [Real.norm_eq_abs, abs_of_nonneg ha, ENNReal.toReal_ofReal hNpos.le]

/-- The real mixed norm is the real value of the finite Mathlib `eLpNorm`. -/
theorem lqSchattenNorm_eq_eLpNorm_toReal {d : ℕ}
    {P : Measure (CoeffSpace d)} {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : SchattenMemLp P N H) (hN : 1 ≤ N) :
    eLpNorm (fun a => absSchattenNorm N (H a)) (ENNReal.ofReal N) P < ⊤ ∧
      0 ≤ lqSchattenNorm P N H ∧
      lqSchattenNorm P N H =
        (eLpNorm (fun a => absSchattenNorm N (H a)) (ENNReal.ofReal N) P).toReal := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp0 : ENNReal.ofReal N ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)
  have hmem := hH.memLp_absSchattenNorm hN
  have hnonneg_moment : 0 ≤ᵐ[P] fun a => absSchattenNorm N (H a) ^ N := by
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    exact Real.rpow_nonneg ha N
  have hnorm_integral_eq :
      (∫ a, ‖absSchattenNorm N (H a)‖ ^ (ENNReal.ofReal N).toReal ∂P) =
        ∫ a, absSchattenNorm N (H a) ^ N ∂P := by
    apply integral_congr_ae
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    simp [Real.norm_eq_abs, abs_of_nonneg ha, ENNReal.toReal_ofReal hNpos.le]
  have hlq_nonneg : 0 ≤ lqSchattenNorm P N H := by
    unfold lqSchattenNorm
    exact Real.rpow_nonneg (integral_nonneg_of_ae hnonneg_moment) N⁻¹
  constructor
  · exact hmem.eLpNorm_lt_top
  constructor
  · exact hlq_nonneg
  · unfold lqSchattenNorm
    rw [hmem.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal]
    · rw [hnorm_integral_eq, ENNReal.toReal_ofReal hNpos.le]
    · rw [hnorm_integral_eq, ENNReal.toReal_ofReal hNpos.le]
      exact Real.rpow_nonneg (integral_nonneg_of_ae hnonneg_moment) N⁻¹

theorem abs_blockMatEntry_le_blockOpNorm (H : BlockMat d) (α β : BlockCoord d) :
    |blockMatEntry H α β| ≤ blockOpNorm H := by
  let M : FullBlockMat d := toFullBlockMat H
  have hentry :
      blockMatEntry H α β = M.mulVec (Pi.single β (1 : ℝ)) α := by
    simp [M, Matrix.mulVec, toFullBlockMat_eq_blockMatEntry]
  calc
    |blockMatEntry H α β| = |M.mulVec (Pi.single β (1 : ℝ)) α| := by rw [hentry]
    _ = ‖(WithLp.toLp (2 : ENNReal) (M.mulVec (Pi.single β (1 : ℝ))) :
          EuclideanSpace ℝ (BlockCoord d)).ofLp α‖ := by
        simp [Real.norm_eq_abs]
    _ ≤ ‖(WithLp.toLp (2 : ENNReal) (M.mulVec (Pi.single β (1 : ℝ))) :
          EuclideanSpace ℝ (BlockCoord d))‖ :=
        PiLp.norm_apply_le _ α
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
          (WithLp.toLp (2 : ENNReal) (Pi.single β (1 : ℝ)))‖ := by
        rw [Matrix.toEuclideanCLM_toLp]
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          ‖(WithLp.toLp (2 : ENNReal) (Pi.single β (1 : ℝ)) :
            EuclideanSpace ℝ (BlockCoord d))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ := by
        simp
    _ = blockOpNorm H := by
        simp [blockOpNorm, M, Matrix.l2_opNorm_toEuclideanCLM]

/-- Each scalar block entry is integrable on a finite measure space. -/
theorem integrable_entry {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : SchattenMemLp P N H) (hN : 1 ≤ N) (α β : BlockCoord d) :
    Integrable (fun a => blockMatEntry (H a) α β) P := by
  have hscalar :
      Integrable (fun a => absSchattenNorm N (H a)) P :=
    (hH.memLp_absSchattenNorm hN).integrable (ENNReal.one_le_ofReal.mpr hN)
  refine hscalar.mono' (hH.measurable α β) ?_
  filter_upwards [hH.symmetric] with a ha
  have hHerm : (toFullBlockMat (H a)).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff (H a)).2 ha
  calc
    ‖blockMatEntry (H a) α β‖ = |blockMatEntry (H a) α β| := Real.norm_eq_abs _
    _ ≤ blockOpNorm (H a) := abs_blockMatEntry_le_blockOpNorm (H a) α β
    _ ≤ absSchattenNorm N (H a) := Analysis.blockOpNorm_le_absSchattenNorm hHerm hN

end SchattenMemLp

namespace Analysis

private theorem l2_opNorm_conjStarAlgAut_for_integrability {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℝ)) (A : Matrix n n ℝ) :
    ‖(Unitary.conjStarAlgAut ℝ _ U) A‖ = ‖A‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary
    (A := (U : Matrix n n ℝ) * A) (hU := Unitary.star_mem U.prop)]
  exact CStarRing.norm_mem_unitary_mul A U.prop

private theorem hermitian_l2_opNorm_eq_eigenvalue_norm_for_integrability {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) :
    ‖toFullBlockMat H‖ = ‖hH.eigenvalues‖ := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [l2_opNorm_conjStarAlgAut_for_integrability]
  simp

private theorem abs_eigenvalue_le_l2_opNorm_for_integrability {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (i : BlockCoord d) :
    |hH.eigenvalues i| ≤ blockOpNorm H := by
  rw [blockOpNorm, hermitian_l2_opNorm_eq_eigenvalue_norm_for_integrability hH]
  simpa [Real.norm_eq_abs] using norm_le_pi_norm hH.eigenvalues i

private theorem eigen_abs_rpow_sum_le_card_mul_blockOpNorm_rpow {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (_hN : 1 ≤ N) :
    (∑ i : BlockCoord d, |hH.eigenvalues i| ^ N) ≤
      (Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H ^ N := by
  calc
    (∑ i : BlockCoord d, |hH.eigenvalues i| ^ N)
        ≤ ∑ _i : BlockCoord d, blockOpNorm H ^ N := by
          refine Finset.sum_le_sum fun i _hi => ?_
          exact Real.rpow_le_rpow (abs_nonneg _)
            (abs_eigenvalue_le_l2_opNorm_for_integrability hH i) (by positivity)
    _ = (Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H ^ N := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- A crude finite-dimensional comparison in the reverse direction from
`blockOpNorm_le_absSchattenNorm`.  The factor depends only on the doubled block dimension and the
exponent; it is used only to prove membership/definedness of subtraction and centering fields,
not as one of the sharp printed constants in the PositiveGap estimate. -/
theorem absSchattenNorm_le_dim_rpow_mul_blockOpNorm {d : ℕ} {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N H ≤ (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm H := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNne : N ≠ 0 := hNpos.ne'
  have hsum_nonneg : 0 ≤ ∑ i : BlockCoord d, |hH.eigenvalues i| ^ N :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) N
  have hop_nonneg : 0 ≤ blockOpNorm H := by
    unfold blockOpNorm
    exact norm_nonneg _
  have hcard_nonneg : 0 ≤ (Fintype.card (BlockCoord d) : ℝ) := by positivity
  have hcard_eq : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp only [BlockCoord, Fintype.card_sum, Fintype.card_fin]
    rw [Nat.cast_add]
    ring
  rw [Analysis.absSchattenNorm_eq_eigenvalues hH, schattenNormEigen]
  calc
    (∑ i : BlockCoord d, |hH.eigenvalues i| ^ N) ^ N⁻¹
        ≤ ((Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H ^ N) ^ N⁻¹ :=
          Real.rpow_le_rpow hsum_nonneg
            (eigen_abs_rpow_sum_le_card_mul_blockOpNorm_rpow hH hN) (by positivity)
    _ = (Fintype.card (BlockCoord d) : ℝ) ^ N⁻¹ * blockOpNorm H := by
          rw [Real.mul_rpow hcard_nonneg (Real.rpow_nonneg hop_nonneg N)]
          rw [← Real.rpow_mul hop_nonneg N N⁻¹, mul_inv_cancel₀ hNne, Real.rpow_one]
    _ = (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm H := by
          rw [hcard_eq]

private theorem blockMatEntry_blockSub (A B : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (blockSub A B) α β = blockMatEntry A α β - blockMatEntry B α β := by
  cases α <;> cases β <;> rfl

private theorem blockTrace_eq_sum_entries (H : BlockMat d) :
    blockTrace H = ∑ α : BlockCoord d, blockMatEntry H α α := by
  simp [blockTrace, Matrix.trace, toFullBlockMat_eq_blockMatEntry]

private theorem integrable_quadratic_form {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α β) P)
    (X : BlockVec d) :
    Integrable (fun a => blockVecDot X (blockMatVecMul (H a) X)) P := by
  rw [show (fun a => blockVecDot X (blockMatVecMul (H a) X)) =
      fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec X α * (blockMatEntry (H a) α β * toFullBlockVec X β) by
    funext a
    exact blockVecDot_blockMatVecMul_eq_sum (H a) X]
  refine integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => ?_
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    ((hH α β).const_mul (toFullBlockVec X α * toFullBlockVec X β))

private theorem blockVecDot_blockMatVecMul_integral {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α β) P)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) X) =
      ∫ a, blockVecDot X (blockMatVecMul (H a) X) ∂P := by
  calc
    blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) X)
        = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec X α *
              ((∫ a, blockMatEntry (H a) α β ∂P) * toFullBlockVec X β) := by
          rw [blockVecDot_blockMatVecMul_eq_sum]
          simp
    _ = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            ∫ a, toFullBlockVec X α *
              (blockMatEntry (H a) α β * toFullBlockVec X β) ∂P := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
    _ = ∫ a, ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec X α * (blockMatEntry (H a) α β * toFullBlockVec X β) ∂P := by
          symm
          rw [MeasureTheory.integral_finsetSum]
          · congr with α
            rw [MeasureTheory.integral_finsetSum]
            intro β _
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              ((hH α β).const_mul (toFullBlockVec X α * toFullBlockVec X β))
          · intro α _
            exact integrable_finsetSum _ fun β _ => by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                ((hH α β).const_mul (toFullBlockVec X α * toFullBlockVec X β))
    _ = ∫ a, blockVecDot X (blockMatVecMul (H a) X) ∂P := by
          apply integral_congr_ae
          exact ae_of_all P fun a => (blockVecDot_blockMatVecMul_eq_sum (H a) X).symm

/-- Constant symmetric blocks are in the real Schatten carrier over a finite law. -/
theorem memLqSchatten_const {d : ℕ} (P : Measure (CoeffSpace d))
    [IsFiniteMeasure P] {N : ℝ} (_hN : 1 ≤ N) (B : BlockMat d)
    (hB : IsSymmetricBlockMat B) : SchattenMemLp P N (fun _ => B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β
    exact aestronglyMeasurable_const
  · exact ae_of_all P fun _ => hB
  · exact integrable_const _

/-- Entrywise Bochner integration commutes with block subtraction. -/
theorem integral_blockSub {d : ℕ} {P : Measure (CoeffSpace d)}
    {F G : CoeffSpace d → BlockMat d}
    (hF : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (F a) α β) P)
    (hG : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (G a) α β) P) :
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (blockSub (F a) (G a)) α β ∂P) =
      blockSub (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P))
        (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)) := by
  change
    ofFullBlockMat
        (Matrix.of fun α β => ∫ a, blockMatEntry (blockSub (F a) (G a)) α β ∂P) =
      ofFullBlockMat
        (Matrix.of fun α β =>
          (∫ a, blockMatEntry (F a) α β ∂P) - ∫ a, blockMatEntry (G a) α β ∂P)
  congr 1
  ext α β
  simp [blockMatEntry_blockSub, MeasureTheory.integral_sub (hF α β) (hG α β)]

/-- The trace of an entrywise Bochner expectation is the expected trace. -/
theorem blockTrace_integral {d : ℕ} {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α β) P) :
    Integrable (fun a => blockTrace (H a)) P ∧
      blockTrace (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) =
        ∫ a, blockTrace (H a) ∂P := by
  have hdiag : ∀ α : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α α) P :=
    fun α => hH α α
  constructor
  · rw [show (fun a => blockTrace (H a)) =
      fun a => ∑ α : BlockCoord d, blockMatEntry (H a) α α by
        funext a
        exact blockTrace_eq_sum_entries (H a)]
    exact integrable_finsetSum _ fun α _ => hdiag α
  · calc
      blockTrace
          (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P))
          = ∑ α : BlockCoord d, ∫ a, blockMatEntry (H a) α α ∂P := by
            simp [blockTrace_eq_sum_entries]
      _ = ∫ a, ∑ α : BlockCoord d, blockMatEntry (H a) α α ∂P := by
            rw [MeasureTheory.integral_finsetSum]
            exact fun α _ => hdiag α
      _ = ∫ a, blockTrace (H a) ∂P := by
            apply integral_congr_ae
            exact ae_of_all P fun a => (blockTrace_eq_sum_entries (H a)).symm

/-- Entrywise Bochner expectation preserves almost-everywhere symmetry. -/
theorem isSymmetricBlockMat_integral {d : ℕ} {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d} (hH : ∀ᵐ a ∂P, IsSymmetricBlockMat (H a)) :
    IsSymmetricBlockMat
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) := by
  intro α β
  simp only [blockMatEntry_ofFullBlockMat, Matrix.of_apply]
  exact integral_congr_ae (hH.mono fun a ha => ha α β)

/-- Entrywise Bochner expectation preserves the block Loewner order. -/
theorem blockMatLoewnerLE_integral {d : ℕ} {P : Measure (CoeffSpace d)}
    {F G : CoeffSpace d → BlockMat d}
    (hF : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (F a) α β) P)
    (hG : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (G a) α β) P)
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    BlockMatLoewnerLE
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P))
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)) := by
  intro X
  rw [blockVecDot_blockMatVecMul_integral hF X,
    blockVecDot_blockMatVecMul_integral hG X]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  exact integral_mono_ae
    ((integrable_quadratic_form hF X).const_mul (1 / 2 : ℝ))
    ((integrable_quadratic_form hG X).const_mul (1 / 2 : ℝ))
    (hFG.mono fun a ha => ha X)

end Analysis

end

end HCPolySupport.HighContrast
end

section
/-!
## Measurability and membership closure for the Schatten norm

EccentricityScaleDecay for the paper's Schatten estimates, on the real exponent
and CG block carriers. The pinned Mathlib supplies the real matrix CFC, but does
not register its isometry for the L2 operator norm. We prove that property from
the spectral representation, then use Mathlib's variable-operator continuity.

Continuity is asserted on symmetric full matrices. The CFC is zero off
that closed set, so its Schatten value is measurable on all full matrices.
Entrywise a.e. measurability therefore suffices, without a circular moment premise.
The dimension factor in the subtraction proof proves finiteness only; it is not
a sharp Schatten triangle inequality or a constant in the printed gap estimate.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub)
namespace HCPolySupport.HighContrast

open MeasureTheory Filter Topology
open scoped BigOperators Matrix.Norms.L2Operator ContinuousFunctionalCalculus

noncomputable section

variable {d : ℕ}

namespace Analysis

private theorem matrix_isometric_cfc {n : Type*} [Fintype n] [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℝ (Matrix n n ℝ) IsSelfAdjoint where
  isometric M hM := by
    have h : M.IsHermitian := hM
    rw [cfcHom_eq_of_continuous_of_map_id hM h.cfcAux
      h.isClosedEmbedding_cfcAux.continuous h.cfcAux_id]
    apply AddMonoidHomClass.isometry_of_norm h.cfcAux
    intro f
    rw [Matrix.IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply]
    rw [CStarRing.norm_mul_mem_unitary
      (hU := Unitary.star_mem h.eigenvectorUnitary.prop)]
    rw [CStarRing.norm_mem_unitary_mul _ h.eigenvectorUnitary.prop]
    rw [Matrix.l2_opNorm_diagonal]
    simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 fun i =>
        f.norm_coe_le_norm ⟨h.eigenvalues i, h.eigenvalues_mem_spectrum_real i⟩
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
      intro x
      have hxmem : (x : ℝ) ∈ Set.range h.eigenvalues := by
        rw [← h.spectrum_real_eq_range_eigenvalues]
        exact x.property
      obtain ⟨i, hi⟩ := hxmem
      have hx : x = ⟨h.eigenvalues i, h.eigenvalues_mem_spectrum_real i⟩ :=
        Subtype.ext hi.symm
      rw [hx]
      exact norm_le_pi_norm
        (fun j : n => f ⟨h.eigenvalues j, h.eigenvalues_mem_spectrum_real j⟩) i

/-- The Schatten norm is continuous on symmetric full blocks, for every
real exponent `N ≥ 1`, including nonintegral exponents and dimension zero. -/
theorem continuousOn_absSchattenNorm {N : ℝ} (hN : 1 ≤ N) :
    ContinuousOn (fun M : FullBlockMat d => absSchattenNorm N (ofFullBlockMat M))
      {M | M.IsHermitian} := by
  let := matrix_isometric_cfc (n := BlockCoord d)
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcfc : ContinuousOn
      (fun M : FullBlockMat d => cfc (fun x : ℝ => |x| ^ N) M)
      {M | M.IsHermitian} := by
    refine ContinuousOn.cfc (s := fun M : FullBlockMat d =>
      Metric.closedBall (0 : ℝ) (‖M‖ + 1)) (fun x : ℝ => |x| ^ N) ?_ ?_ ?_ ?_ ?_
    · intro M _
      exact isCompact_closedBall _ _
    · exact continuous_id.continuousOn
    · intro M _
      have hn : ∀ᶠ M' : FullBlockMat d in 𝓝 M, ‖M'‖ < ‖M‖ + 1 :=
        continuous_norm.continuousAt.eventually
          (isOpen_Iio.mem_nhds (by simp))
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with M' hM' hHerm
      intro x hx
      exact Metric.mem_closedBall.mpr (by
        simpa [Real.dist_eq, abs_sub_comm] using
          (IsometricContinuousFunctionalCalculus.norm_spectrum_le M' hx hHerm).trans hM'.le)
    · intro M hM
      exact hM
    · intro M _
      exact ((Real.continuous_rpow_const hNpos.le).comp continuous_abs).continuousOn
  have ht := (Continuous.matrix_trace continuous_id).comp_continuousOn hcfc
  simpa only [absSchattenNorm, toFullBlockMat_ofFullBlockMat] using!
    (Real.continuous_rpow_const (inv_nonneg.mpr hNpos.le)).comp_continuousOn ht

/-- Borel measurability on all full blocks uses the zero convention off
the closed set of symmetric matrices; global continuity is not asserted. The
explicit function type is CG's `FullBlockMat d` unfolded to expose its entrywise
Borel sigma algebra, without adding an instance or a carrier. -/
theorem measurable_absSchattenNorm {N : ℝ} (hN : 1 ≤ N) :
    Measurable (fun M : BlockCoord d → BlockCoord d → ℝ =>
      absSchattenNorm N (ofFullBlockMat M)) := by
  classical
  have hOM : OpensMeasurableSpace (BlockCoord d → BlockCoord d → ℝ) := inferInstance
  have hs : MeasurableSet {M : BlockCoord d → BlockCoord d → ℝ | Matrix.IsHermitian M} := by
    exact @IsClosed.measurableSet _ _ _ _ hOM
      (isClosed_eq (f := fun M : BlockCoord d → BlockCoord d → ℝ =>
        Matrix.conjTranspose M) continuous_id.matrix_conjTranspose continuous_id)
  have hc : ContinuousOn (fun M : BlockCoord d → BlockCoord d → ℝ =>
      absSchattenNorm N (ofFullBlockMat M)) {M | Matrix.IsHermitian M} :=
    continuousOn_absSchattenNorm hN
  have hp := hc.measurable_piecewise
    (g := fun _ => (0 : ℝ)) continuous_const.continuousOn hs
  convert hp using 1
  funext M
  by_cases hM : M ∈ {M : BlockCoord d → BlockCoord d → ℝ | Matrix.IsHermitian M}
  · simp [Set.piecewise_eq_of_mem _ _ _ hM]
  · have hM' : ¬ @IsSelfAdjoint (FullBlockMat d) _ M := hM
    simp [Set.piecewise_eq_of_notMem _ _ _ hM, absSchattenNorm, toFullBlockMat_ofFullBlockMat M,
      cfc_apply_of_not_predicate (A := FullBlockMat d) M hM',
      Real.zero_rpow (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hN)))]

/-- The a.e. measurability bridge depends on the entrywise measurability
premise alone, so it applies in particular to a.e. symmetric fields before their
moment integrability has been established. -/
theorem aestronglyMeasurable_absSchattenNorm {P : Measure (CoeffSpace d)}
    {F : CoeffSpace d → BlockMat d} (hF : HasMeasurableBlock P F)
    {N : ℝ} (hN : 1 ≤ N) :
    AEStronglyMeasurable (fun ω => absSchattenNorm N (F ω)) P := by
  have hm : AEMeasurable (fun ω α β => toFullBlockMat (F ω) α β) P :=
    AEMeasurable.of_eval fun α =>
      AEMeasurable.of_eval fun β => (hF α β).aemeasurable
  simpa only [Function.comp_def, ofFullBlockMat_toFullBlockMat] using
    ((measurable_absSchattenNorm (d := d) hN).comp_aemeasurable hm).aestronglyMeasurable

end Analysis

namespace SchattenMemLp

private theorem entry_sub (A B : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (blockSub A B) α β = blockMatEntry A α β - blockMatEntry B α β := by
  cases α <;> cases β <;> rfl

private theorem full_sub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

/-- Subtraction preserves the real Schatten moment carrier on any measure
space. The crude factor `(2*d)^(1/N)` is used only for moment finiteness, and
does not supply the sharp triangle inequality in the printed gap estimate. -/
theorem sub {P : Measure (CoeffSpace d)} {N : ℝ}
    {F G : CoeffSpace d → BlockMat d}
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G) (hN : 1 ≤ N) :
    SchattenMemLp P N (fun a => blockSub (F a) (G a)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hm : HasMeasurableBlock P (fun a => blockSub (F a) (G a)) := by
    intro α β
    simp only [entry_sub]
    exact (hF.measurable α β).sub (hG.measurable α β)
  have hs : ∀ᵐ a ∂P, IsSymmetricBlockMat (blockSub (F a) (G a)) := by
    filter_upwards [hF.symmetric, hG.symmetric] with a ha hb
    intro α β
    rw [entry_sub, entry_sub, ha α β, hb α β]
  have hsm := Analysis.aestronglyMeasurable_absSchattenNorm hm hN
  have hdom := ((hF.memLp_absSchattenNorm hN).add
    (hG.memLp_absSchattenNorm hN)).const_mul ((2 * (d : ℝ)) ^ N⁻¹)
  have hmem : MemLp (fun a => absSchattenNorm N (blockSub (F a) (G a)))
      (ENNReal.ofReal N) P := by
    apply hdom.mono' hsm
    filter_upwards [hF.symmetric, hG.symmetric, hs] with a ha hb hab
    have hA := (Analysis.toFullBlockMat_isHermitian_iff (F a)).2 ha
    have hB := (Analysis.toFullBlockMat_isHermitian_iff (G a)).2 hb
    have hAB := (Analysis.toFullBlockMat_isHermitian_iff _).2 hab
    rw [Real.norm_eq_abs, abs_of_nonneg (Analysis.absSchattenNorm_nonneg hAB hN)]
    calc
      absSchattenNorm N (blockSub (F a) (G a))
          ≤ (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm (blockSub (F a) (G a)) :=
        Analysis.absSchattenNorm_le_dim_rpow_mul_blockOpNorm hAB hN
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * (blockOpNorm (F a) + blockOpNorm (G a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [blockOpNorm, full_sub] using
          norm_sub_le (toFullBlockMat (F a)) (toFullBlockMat (G a))
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * (absSchattenNorm N (F a) + absSchattenNorm N (G a)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (Analysis.blockOpNorm_le_absSchattenNorm hA hN)
            (Analysis.blockOpNorm_le_absSchattenNorm hB hN)) (by positivity)
  refine ⟨hm, hs, ?_⟩
  have hi := (integrable_norm_rpow_iff hsm
    (ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)) ENNReal.ofReal_ne_top).2 hmem
  apply hi.congr
  filter_upwards [hs] with a ha
  have hA := (Analysis.toFullBlockMat_isHermitian_iff _).2 ha
  simp [Real.norm_eq_abs, abs_of_nonneg (Analysis.absSchattenNorm_nonneg hA hN),
    ENNReal.toReal_ofReal hNpos.le]

/-- Centering by the entrywise expectation preserves membership on a finite
measure space. This uses subtraction closure and symmetry of the mean, with no
additional moment or measurability premise. -/
theorem center {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {N : ℝ}
    {H : CoeffSpace d → BlockMat d} (hH : SchattenMemLp P N H) (hN : 1 ≤ N) :
    SchattenMemLp P N (fun a => blockSub (H a)
      (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (H b) α β ∂P))) := by
  exact hH.sub (Analysis.memLqSchatten_const P hN _
    (Analysis.isSymmetricBlockMat_integral hH.symmetric)) hN

end SchattenMemLp

end

end HCPolySupport.HighContrast
end

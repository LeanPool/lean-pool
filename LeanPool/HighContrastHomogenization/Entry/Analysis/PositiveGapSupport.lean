/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Setup.Profile
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

/-!
# High-contrast homogenization: Entry.Analysis.PositiveGapSupport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positive Gap EccentricityScaleDecay

The scalar, pointwise and mixed-norm estimates the positive-gap theorem
`l.fixed.geometry.positive.gap` is assembled from: the mean-penalty bounds, the pointwise gap
inequality, the scalar moment inequalities and the norm comparison.  The mixed-norm
subtraction estimate also underlies the matrix-averaging lemma
`l.fixed.geometry.matrix.averaging`.
-/

section
/-!
## Elementary bounds for the mean penalty

This section proves the deterministic O7 sign consequence from the printed hypothesis
`I ≤ M`: the natural-power mean penalty is nonnegative on every symmetric block above the
block identity.  The stochastic specialization to normalized adapted means is supplied by
the mean-order consequences once the source integrability and order hypotheses are available.
-/

open HCPolySupport.HighContrast (blockSub blockTrace)
namespace HCPolySupport.HighContrast.Analysis

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem full_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

private theorem blockMatLoewnerLE_toFull_le {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) : toFullBlockMat A ≤ toFullBlockMat B := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
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
  have hdiff :
      blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
        blockVecDot X (blockMatVecMul B X) -
          blockVecDot X (blockMatVecMul A X) := by
    simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
  have hle := hAB X
  change 0 ≤ dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q)
  rw [hquad, hdiff]
  linarith only [hle]

private theorem blockIdentity_hermitian :
    (toFullBlockMat (Book.Ch02.blockIdentity d)).IsHermitian := by
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  rw [hI]
  exact Matrix.isHermitian_one

/-- If a symmetric block lies above the block identity, then its printed trace excess is
nonnegative. -/
theorem blockTrace_identity_sub_nonneg (M : BlockMat d)
    (hM : IsSymmetricBlockMat M)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M) :
    0 ≤ blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := by
  have hMH : (toFullBlockMat M).IsHermitian := (toFullBlockMat_isHermitian_iff M).2 hM
  have horder := blockMatLoewnerLE_toFull_le blockIdentity_hermitian hMH hIM
  have hdiff : (toFullBlockMat (blockSub M (Book.Ch02.blockIdentity d))).PosSemidef := by
    rw [full_blockSub]
    exact (Matrix.le_iff).mp horder
  exact blockTrace_nonneg hdiff

/-- O7's deterministic sign: the natural-power mean penalty is nonnegative on
symmetric blocks above the identity. -/
theorem meanPenalty_nonneg (Q : ℕ) (M : BlockMat d)
    (hM : IsSymmetricBlockMat M)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M) :
    0 ≤ meanPenalty Q M := by
  have ht : 0 ≤ blockTrace (blockSub M (Book.Ch02.blockIdentity d)) :=
    blockTrace_identity_sub_nonneg M hM hIM
  have hone : 1 ≤ 1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d)) := by
    linarith only [ht]
  have hpow : 1 ≤ (1 + blockTrace (blockSub M (Book.Ch02.blockIdentity d))) ^ Q :=
    one_le_pow₀ hone
  unfold meanPenalty
  linarith only [hpow]

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Pointwise matrix inequalities for the PositiveGap support layer

This file keeps the deterministic block-matrix part separate from the later
random-field assembly.  The fixed block operations are used throughout.
-/

open HCPolySupport.HighContrast (blockSub blockTrace)
namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

private theorem toFullBlockMat_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

private theorem blockSub_eq_ofFullBlockMat_sub (A B : BlockMat d) :
    blockSub A B = ofFullBlockMat (toFullBlockMat A - toFullBlockMat B) := by
  cases A
  cases B
  rfl

private theorem blockLoewnerLE_to_matrixOrder {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) :
    toFullBlockMat A ≤ toFullBlockMat B := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
  intro q
  change 0 ≤ dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q)
  let X : BlockVec d := ofFullBlockVec q
  have hquad :
      dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q) =
        blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) := by
    rw [← dotProduct_toFullBlockVec X
      (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X)]
    rw [toFullBlockVec_blockMatVecMul]
    simp [X]
  have hdiff :
      blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
        blockVecDot X (blockMatVecMul B X) -
          blockVecDot X (blockMatVecMul A X) := by
    simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
  have horder := hAB X
  rw [hquad, hdiff]
  linarith only [horder]

private theorem blockLoewnerLE_sub_posSemidef {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) :
    (toFullBlockMat (blockSub B A)).PosSemidef := by
  have horder := blockLoewnerLE_to_matrixOrder hA hB hAB
  rw [toFullBlockMat_blockSub]
  exact (Matrix.le_iff).mp horder

theorem ordered_gap_posSemidef {d : ℕ} {F G : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hG : IsSymmetricBlockMat G)
    (hFpos : BlockMatLoewnerLE (ofFullBlockMat 0) F)
    (hFG : BlockMatLoewnerLE F G) :
    (toFullBlockMat (blockSub G F)).PosSemidef ∧
      (toFullBlockMat G).PosSemidef ∧
      BlockMatLoewnerLE (blockSub G F) G := by
  let hFh : (toFullBlockMat F).IsHermitian := (toFullBlockMat_isHermitian_iff F).2 hF
  let hGh : (toFullBlockMat G).IsHermitian := (toFullBlockMat_isHermitian_iff G).2 hG
  have h0h : (toFullBlockMat (ofFullBlockMat (0 : FullBlockMat d))).IsHermitian := by
    simp
  have hFpsd : (toFullBlockMat F).PosSemidef := by
    convert blockLoewnerLE_sub_posSemidef h0h hFh hFpos using 1
    rw [toFullBlockMat_blockSub]
    simp
  have hDpsd : (toFullBlockMat (blockSub G F)).PosSemidef :=
    blockLoewnerLE_sub_posSemidef hFh hGh hFG
  have hGpsd : (toFullBlockMat G).PosSemidef := by
    have hsum : (toFullBlockMat F + toFullBlockMat (blockSub G F)).PosSemidef :=
      hFpsd.add hDpsd
    convert hsum using 1
    rw [toFullBlockMat_blockSub]
    ext α β
    simp
  refine ⟨hDpsd, hGpsd, ?_⟩
  intro X
  have hFquad :
      0 ≤ blockVecDot X (blockMatVecMul F X) := by
    have h := hFpsd.dotProduct_mulVec_nonneg (toFullBlockVec X)
    have h' :
        0 ≤ dotProduct (toFullBlockVec X)
          (Matrix.mulVec (toFullBlockMat F) (toFullBlockVec X)) := by
      simpa [dotProduct] using h
    rw [← toFullBlockVec_blockMatVecMul,
      dotProduct_toFullBlockVec X (blockMatVecMul F X)] at h'
    exact h'
  have hDquad :
      blockVecDot X (blockMatVecMul (blockSub G F) X) =
        blockVecDot X (blockMatVecMul G X) -
          blockVecDot X (blockMatVecMul F X) := by
    rw [blockSub_eq_ofFullBlockMat_sub G F]
    simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub G F X
  rw [hDquad]
  linarith only [hFquad]

/-- Monotonicity of the real L2 operator norm on positive semidefinite blocks. -/
theorem blockOpNorm_mono_of_posSemidef {D G : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef)
    (hG : (toFullBlockMat G).IsHermitian) (hDG : BlockMatLoewnerLE D G) :
    blockOpNorm D ≤ blockOpNorm G := by
  have hdiff := (Matrix.le_iff).mp (blockLoewnerLE_to_matrixOrder hD.isHermitian hG hDG)
  let U := hD.isHermitian.eigenvectorUnitary
  have hdiag (i : BlockCoord d) : hD.isHermitian.eigenvalues i ≤
      (Unitary.conjStarAlgAut ℝ _ (star U) (toFullBlockMat G)) i i := by
    have hp := (hdiff.conjTranspose_mul_mul_same (U : FullBlockMat d)).diag_nonneg (i := i)
    have heq := hD.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    have hsub := map_sub (Unitary.conjStarAlgAut ℝ _ (star U))
      (toFullBlockMat G) (toFullBlockMat D)
    have hps : 0 ≤ (Unitary.conjStarAlgAut ℝ _ (star U)
        (toFullBlockMat G - toFullBlockMat D)) i i := hp
    rw [hsub, heq] at hps
    simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Function.comp_apply,
      RCLike.ofReal_real_eq_id, id_eq, sub_nonneg] using hps
  unfold blockOpNorm
  rw [hermitian_norm_eq_eigenvalue_norm hD.isHermitian]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [Real.norm_of_nonneg (hD.eigenvalues_nonneg i)]
  exact (hdiag i).trans (hermitian_conj_diagonal_le_norm hG (star U) i)

/-- The first display of the positive-gap proof, valid already for real `N ≥ 1`. -/
theorem absSchattenNorm_gap_le_opNorm_rpow_mul_trace_rpow {D G : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef)
    (hG : (toFullBlockMat G).IsHermitian) (hDG : BlockMatLoewnerLE D G)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N D ≤ blockOpNorm G ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have heig (i : BlockCoord d) : hD.isHermitian.eigenvalues i ≤ blockOpNorm G := by
    calc
      _ ≤ ‖hD.isHermitian.eigenvalues‖ := by
        simpa only [Real.norm_of_nonneg (hD.eigenvalues_nonneg i)] using
          norm_le_pi_norm hD.isHermitian.eigenvalues i
      _ = blockOpNorm D := (hermitian_norm_eq_eigenvalue_norm hD.isHermitian).symm
      _ ≤ blockOpNorm G := blockOpNorm_mono_of_posSemidef hD hG hDG
  have hsum : ∑ i, |hD.isHermitian.eigenvalues i| ^ N ≤
      blockOpNorm G ^ (N - 1) * blockTrace D := by
    rw [blockTrace, hD.isHermitian.trace_eq_sum_eigenvalues, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_of_nonneg (hD.eigenvalues_nonneg i)]
    calc
      _ = hD.isHermitian.eigenvalues i ^ (N - 1) * hD.isHermitian.eigenvalues i := by
        rw [← Real.rpow_add_one' (hD.eigenvalues_nonneg i)
          (by simpa only [sub_add_cancel] using hNpos.ne'), sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hD.eigenvalues_nonneg i) (heig i) (sub_nonneg.mpr hN))
        (hD.eigenvalues_nonneg i)
  rw [absSchattenNorm_eq_eigenvalues hD.isHermitian, schattenNormEigen]
  calc
    _ ≤ (blockOpNorm G ^ (N - 1) * blockTrace D) ^ N⁻¹ :=
      Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _))
        hsum (inv_nonneg.mpr hNpos.le)
    _ = _ := by
      unfold blockOpNorm
      rw [Real.mul_rpow (Real.rpow_nonneg (norm_nonneg (toFullBlockMat G)) _) (blockTrace_nonneg
        hD),
        ← Real.rpow_mul (norm_nonneg (toFullBlockMat G))]
      congr 2
      field_simp [hNpos.ne']

/-- Sharp trace/Schatten comparison with the printed `2d` factor, including `d = 0`. -/
theorem trace_le_dim_rpow_mul_absSchattenNorm {D : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef) {N : ℝ} (hN : 1 ≤ N) :
    blockTrace D ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) * absSchattenNorm N D := by
  have hh := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hN
    (fun _ : BlockCoord d => (1 : ℝ)) hD.isHermitian.eigenvalues
    (fun _ => zero_le_one) hD.eigenvalues_nonneg
  rw [blockTrace, hD.isHermitian.trace_eq_sum_eigenvalues,
    absSchattenNorm_eq_eigenvalues hD.isHermitian, schattenNormEigen]
  simpa only [one_mul, abs_of_nonneg (hD.eigenvalues_nonneg _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, BlockCoord, Fintype.card_sum,
    Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ← two_mul] using! hh

/-- The trace interpolation used for the deterministic mean gap in the centering step. -/
theorem ordered_trace_le_dim_rpow_mul_opNorm_rpow_mul_trace_rpow {D G : BlockMat d}
    (hD : (toFullBlockMat D).PosSemidef)
    (hG : (toFullBlockMat G).IsHermitian) (hDG : BlockMatLoewnerLE D G)
    {N : ℝ} (hN : 1 ≤ N) :
    blockTrace D ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) *
      blockOpNorm G ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ := by
  calc
    _ ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) * absSchattenNorm N D :=
      trace_le_dim_rpow_mul_absSchattenNorm hD hN
    _ ≤ (2 * (d : ℝ)) ^ (1 - N⁻¹) *
        (blockOpNorm G ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹) :=
      mul_le_mul_of_nonneg_left (absSchattenNorm_gap_le_opNorm_rpow_mul_trace_rpow hD hG hDG hN)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := (mul_assoc _ _ _).symm

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Scalar moment inequalities for the PositiveGap support layer

This file records scalar `MemLp` consequences that do not depend on the
operator-valued Schatten infrastructure.
-/

namespace HCPolySupport.HighContrast.Analysis

open MeasureTheory

noncomputable section

private theorem scalar_holderConjugate_power {N : ℝ} (hN : 1 < N) :
    (N / (N - 1)).HolderConjugate N := by
  have hp : 1 < N / (N - 1) := by
    have hden : 0 < N - 1 := by linarith only [hN]
    rw [lt_div_iff₀ hden]
    linarith only [hN]
  rw [Real.holderConjugate_iff_eq_conjExponent hp]
  have hdenne : N - 1 ≠ 0 := by linarith only [hN]
  field_simp [hdenne]
  ring

private theorem scalar_power_memLp_conjugate {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 1 < N) {f : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf : MemLp f (ENNReal.ofReal N) μ) :
    MemLp (fun x => f x ^ (N - 1)) (ENNReal.ofReal (N / (N - 1))) μ := by
  have hqpos : 0 < N - 1 := by linarith only [hN]
  have hbase :
      MemLp (fun x => ‖f x‖ ^ (N - 1)) (ENNReal.ofReal (N / (N - 1))) μ := by
    convert hf.norm_rpow_div (ENNReal.ofReal (N - 1)) using 1
    · ext x
      rw [ENNReal.toReal_ofReal hqpos.le]
    · rw [ENNReal.ofReal_div_of_pos hqpos]
  exact (memLp_congr_ae (by
    filter_upwards [hf_nonneg] with x hx
    rw [Real.norm_of_nonneg hx])).mp hbase

theorem scalar_holder_power_integrable_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 1 < N) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : MemLp f (ENNReal.ofReal N) μ) (hg : MemLp g (ENNReal.ofReal N) μ) :
    Integrable (fun x => f x ^ (N - 1) * g x) μ ∧
      ∫ x, f x ^ (N - 1) * g x ∂μ ≤
        (∫ x, (f x ^ (N - 1)) ^ (N / (N - 1)) ∂μ) ^ (1 / (N / (N - 1))) *
          (∫ x, g x ^ N ∂μ) ^ (1 / N) := by
  have hpq : (N / (N - 1)).HolderConjugate N := scalar_holderConjugate_power hN
  have hfpow := scalar_power_memLp_conjugate hN hf_nonneg hf
  have : ENNReal.HolderTriple (ENNReal.ofReal (N / (N - 1))) (ENNReal.ofReal N) 1 :=
    hpq.ennrealOfReal
  have hint : Integrable (fun x => f x ^ (N - 1) * g x) μ := hfpow.integrable_mul hg
  refine ⟨hint, ?_⟩
  have hfpow_nonneg : 0 ≤ᵐ[μ] fun x => f x ^ (N - 1) := by
    filter_upwards [hf_nonneg] with x hx
    exact Real.rpow_nonneg hx _
  exact integral_mul_le_Lp_mul_Lq_of_nonneg hpq hfpow_nonneg hg_nonneg hfpow hg

theorem scalar_minkowski_toReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {N : ℝ} (hN : 1 ≤ N) {f g : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal N) μ) (hg : MemLp g (ENNReal.ofReal N) μ) :
    MemLp (fun x => f x + g x) (ENNReal.ofReal N) μ ∧
      (eLpNorm (fun x => f x + g x) (ENNReal.ofReal N) μ).toReal ≤
        (eLpNorm f (ENNReal.ofReal N) μ).toReal +
          (eLpNorm g (ENNReal.ofReal N) μ).toReal := by
  have hp1 : 1 ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hN
  have hmem : MemLp (fun x => f x + g x) (ENNReal.ofReal N) μ := by
    simpa only [Pi.add_apply] using! hf.add hg
  refine ⟨hmem, ?_⟩
  have hle :
      eLpNorm (fun x => f x + g x) (ENNReal.ofReal N) μ ≤
        eLpNorm f (ENNReal.ofReal N) μ + eLpNorm g (ENNReal.ofReal N) μ := by
    simpa only [Pi.add_apply] using!
      eLpNorm_add_le hp1
  have htop :
      eLpNorm f (ENNReal.ofReal N) μ + eLpNorm g (ENNReal.ofReal N) μ ≠ ⊤ := by
    exact ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono htop hle

/-- Identify the real scalar norm with the rooted moment on its natural nonnegative domain. -/
theorem scalar_eLpNorm_toReal_eq_root {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 0 < N) {f : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf : MemLp f (ENNReal.ofReal N) μ) :
    (eLpNorm f (ENNReal.ofReal N) μ).toReal = (∫ x, f x ^ N ∂μ) ^ N⁻¹ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hN)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hN.le]
  have heq : (∫ x, ‖f x‖ ^ N ∂μ) = ∫ x, f x ^ N ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf_nonneg] with x hx
    rw [Real.norm_of_nonneg hx]
  rw [heq, ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg_of_ae
    (hf_nonneg.mono (fun x hx => Real.rpow_nonneg hx _))) _)]

/-- The rooted mixed-moment Hölder estimate used in the positive-gap proof. -/
theorem scalar_mixedMoment_root_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {N : ℝ} (hN : 1 < N) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : MemLp f (ENNReal.ofReal N) μ) (hg : MemLp g (ENNReal.ofReal N) μ) :
    (∫ x, f x ^ (N - 1) * g x ∂μ) ^ N⁻¹ ≤
      (eLpNorm f (ENNReal.ofReal N) μ).toReal ^ (1 - N⁻¹) *
        (eLpNorm g (ENNReal.ofReal N) μ).toReal ^ N⁻¹ := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hNm : N - 1 ≠ 0 := (sub_pos.mpr hN).ne'
  have hflat : (∫ x, (f x ^ (N - 1)) ^ (N / (N - 1)) ∂μ) = ∫ x, f x ^ N ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf_nonneg] with x hx
    rw [← Real.rpow_mul hx]
    congr 1
    field_simp
  have hfp : 0 ≤ ∫ x, f x ^ N ∂μ :=
    integral_nonneg_of_ae (hf_nonneg.mono (fun x hx => Real.rpow_nonneg hx _))
  have hgp : 0 ≤ ∫ x, g x ^ N ∂μ :=
    integral_nonneg_of_ae (hg_nonneg.mono (fun x hx => Real.rpow_nonneg hx _))
  have hm : 0 ≤ ∫ x, f x ^ (N - 1) * g x ∂μ :=
    integral_nonneg_of_ae (by
      filter_upwards [hf_nonneg, hg_nonneg] with x hx hy
      exact mul_nonneg (Real.rpow_nonneg hx _) hy)
  have hh := (scalar_holder_power_integrable_bound hN hf_nonneg hg_nonneg hf hg).2
  rw [hflat] at hh
  have he : 1 / (N / (N - 1)) = N⁻¹ * (N - 1) := by field_simp
  rw [he, Real.rpow_mul hfp, one_div] at hh
  have hr := Real.rpow_le_rpow hm hh (inv_nonneg.mpr hNpos.le)
  rw [Real.mul_rpow (Real.rpow_nonneg (Real.rpow_nonneg hfp _) _) (Real.rpow_nonneg hgp _),
    ← Real.rpow_mul (Real.rpow_nonneg hfp _)] at hr
  have he' : (N - 1) * N⁻¹ = 1 - N⁻¹ := by field_simp
  rw [he'] at hr
  rw [scalar_eLpNorm_toReal_eq_root hNpos hf_nonneg hf,
    scalar_eLpNorm_toReal_eq_root hNpos hg_nonneg hg]
  exact hr

/-- Scalar Young inequality in the precise mixed-power form used for absorption. -/
theorem scalar_young_mixed {N x y : ℝ} (hN : 1 < N) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y ^ (1 - N⁻¹) * x ^ N⁻¹ ≤ (1 - N⁻¹) * y + N⁻¹ * x := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hNm : N - 1 ≠ 0 := (sub_pos.mpr hN).ne'
  have he : 1 - N⁻¹ = (N / (N - 1))⁻¹ := by field_simp
  rw [he]
  have hh := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg hy (N / (N - 1))⁻¹) (Real.rpow_nonneg hx N⁻¹)
    (scalar_holderConjugate_power hN)
  rw [Real.rpow_inv_rpow hy (div_ne_zero hNpos.ne' hNm),
    Real.rpow_inv_rpow hx hNpos.ne'] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Young absorption with the exact factor `N / (N - 1)`. -/
theorem scalar_young_absorb {N x y a : ℝ} (hN : 1 < N) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ a + y ^ (1 - N⁻¹) * x ^ N⁻¹) :
    x ≤ y + N / (N - 1) * a := by
  have hh := h.trans (add_le_add le_rfl (scalar_young_mixed hN hx hy))
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hcoef : 0 < 1 - N⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hN)
  have he : N / (N - 1) = (1 - N⁻¹)⁻¹ := by field_simp
  rw [he]
  apply (mul_le_mul_iff_right₀ hcoef).mp
  calc
    (1 - N⁻¹) * x ≤ (1 - N⁻¹) * y + a := by linarith only [hh]
    _ = (1 - N⁻¹) * (y + (1 - N⁻¹)⁻¹ * a) := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hcoef.ne', one_mul]

/-- Subadditivity of the exponent in the printed positive-gap interpolation. -/
theorem scalar_gap_power_add_le {N a b : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ (1 - N⁻¹) ≤ a ^ (1 - N⁻¹) + b ^ (1 - N⁻¹) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  exact Real.rpow_add_le_add_rpow ha hb
    (sub_nonneg.mpr ((inv_le_one₀ hNpos).mpr hN))
    (sub_le_self _ (inv_nonneg.mpr hNpos.le))

/-- The paper's exact dimension coefficient after Young absorption; `m` is `2d`. -/
theorem scalar_gap_young_absorb {N m x y a : ℝ} (hN : 1 < N)
    (hm : 0 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ a + m ^ ((N - 1) / N ^ 2) * y ^ (1 - N⁻¹) * x ^ N⁻¹) :
    x ≤ m ^ N⁻¹ * y + N / (N - 1) * a := by
  apply scalar_young_absorb hN hx (mul_nonneg (Real.rpow_nonneg hm _) hy)
  rw [Real.mul_rpow (Real.rpow_nonneg hm _) hy, ← Real.rpow_mul hm]
  have he : N⁻¹ * (1 - N⁻¹) = (N - 1) / N ^ 2 := by field_simp
  rwa [he]

/-- The rational factor in the last line of the printed proof. -/
theorem scalar_gap_absorption_factor_le_two {N : ℝ} (hN : 2 ≤ N) :
    N / (N - 1) ≤ 2 := by
  apply (div_le_iff₀ (by linarith only [hN] : 0 < N - 1)).mpr
  linarith only [hN]

/-- The dimension simplification in the last line of the printed proof. -/
theorem scalar_gap_dimension_factor_le {N m : ℝ} (hN : 1 ≤ N) (hm : 0 ≤ m) :
    (2 * m) ^ (1 - N⁻¹) ≤ 2 * m ^ (1 - N⁻¹) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hm _)
  calc
    (2 : ℝ) ^ (1 - N⁻¹) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (sub_le_self _ (inv_nonneg.mpr (zero_le_one.trans hN)))
    _ = 2 := Real.rpow_one _

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Real mixed Schatten norm bridges for the PositiveGap assembly

This file contains only the random-norm consequences needed for the
PositiveGap result: the coefficient-one subtraction estimate and the exact
constant-field readback on a probability law.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub)
namespace HCPolySupport.HighContrast.Analysis

open MeasureTheory

noncomputable section

/-- Sharp random-field subtraction for the real Schatten mixed norm. -/
theorem lqSchattenNorm_sub_le {d : ℕ} {P : Measure (CoeffSpace d)}
    {N : ℝ} (hN : 1 ≤ N) {F G : CoeffSpace d → BlockMat d}
    (hF : SchattenMemLp P N F) (hG : SchattenMemLp P N G) :
    lqSchattenNorm P N (fun a => blockSub (F a) (G a)) ≤
      lqSchattenNorm P N F + lqSchattenNorm P N G := by
  have hD : SchattenMemLp P N (fun a => blockSub (F a) (G a)) := hF.sub hG hN
  have hFmem := hF.memLp_absSchattenNorm hN
  have hGmem := hG.memLp_absSchattenNorm hN
  have hDread := hD.lqSchattenNorm_eq_eLpNorm_toReal hN
  have hFread := hF.lqSchattenNorm_eq_eLpNorm_toReal hN
  have hGread := hG.lqSchattenNorm_eq_eLpNorm_toReal hN
  have hsum := scalar_minkowski_toReal hN hFmem hGmem
  have hpoint :
      ∀ᵐ a ∂P,
        ‖absSchattenNorm N (blockSub (F a) (G a))‖ ≤
          ‖absSchattenNorm N (F a) + absSchattenNorm N (G a)‖ := by
    filter_upwards [hF.symmetric, hG.symmetric, hD.symmetric] with a hFa hGa hDa
    have hFH := (toFullBlockMat_isHermitian_iff (F a)).2 hFa
    have hGH := (toFullBlockMat_isHermitian_iff (G a)).2 hGa
    have hDH := (toFullBlockMat_isHermitian_iff (blockSub (F a) (G a))).2 hDa
    have hle := absSchattenNorm_sub_le hFH hGH hN
    have hDnn := absSchattenNorm_nonneg hDH hN
    have hFnn := absSchattenNorm_nonneg hFH hN
    have hGnn := absSchattenNorm_nonneg hGH hN
    rw [Real.norm_eq_abs, abs_of_nonneg hDnn, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hFnn hGnn)]
    exact hle
  have hmono :
      (eLpNorm (fun a => absSchattenNorm N (blockSub (F a) (G a)))
          (ENNReal.ofReal N) P).toReal ≤
        (eLpNorm (fun a => absSchattenNorm N (F a) + absSchattenNorm N (G a))
          (ENNReal.ofReal N) P).toReal :=
    ENNReal.toReal_mono hsum.1.eLpNorm_ne_top
      (eLpNorm_mono_ae (hD.memLp_absSchattenNorm hN).aestronglyMeasurable hpoint)
  calc
    lqSchattenNorm P N (fun a => blockSub (F a) (G a))
        = (eLpNorm (fun a => absSchattenNorm N (blockSub (F a) (G a)))
            (ENNReal.ofReal N) P).toReal := hDread.2.2
    _ ≤ (eLpNorm (fun a => absSchattenNorm N (F a) + absSchattenNorm N (G a))
          (ENNReal.ofReal N) P).toReal := hmono
    _ ≤ (eLpNorm (fun a => absSchattenNorm N (F a)) (ENNReal.ofReal N) P).toReal +
          (eLpNorm (fun a => absSchattenNorm N (G a)) (ENNReal.ofReal N) P).toReal := hsum.2
    _ = lqSchattenNorm P N F + lqSchattenNorm P N G := by
      rw [hFread.2.2, hGread.2.2]

/-- On a probability law, the mixed norm of a deterministic symmetric block is
its deterministic Schatten norm. -/
theorem lqSchattenNorm_const {d : ℕ} (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] {N : ℝ} (hN : 1 ≤ N)
    (B : BlockMat d) (hB : IsSymmetricBlockMat B) :
    lqSchattenNorm P N (fun _ => B) = absSchattenNorm N B := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hBH := (toFullBlockMat_isHermitian_iff B).2 hB
  have hBnn : 0 ≤ absSchattenNorm N B := absSchattenNorm_nonneg hBH hN
  unfold lqSchattenNorm
  rw [integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  exact Real.rpow_rpow_inv hBnn hNpos.ne'

end

end HCPolySupport.HighContrast.Analysis
end

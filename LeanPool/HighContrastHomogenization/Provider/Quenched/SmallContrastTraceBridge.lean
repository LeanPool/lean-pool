/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AlignedSubdivisionQuadraticGap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastAntitone
public import LeanPool.HighContrastHomogenization.Provider.Persistence.AdaptedPersistence
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate
public import Mathlib.Tactic.NoncommRing

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastTraceBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Trace scalarization for the sharp fluctuation

The sharp fluctuation has a normalized trace consisting of the hatted Schur
defect and a separate term measuring the symmetric part of the Schur coupling.
The latter term is retained explicitly.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem trace_fromBlocks (A B C D : Mat d) :
    Matrix.trace (Matrix.fromBlocks A B C D : FullBlockMat d) =
      Matrix.trace A + Matrix.trace D := by
  simp only [Matrix.trace, Fintype.sum_sum_type, Matrix.diag_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

private theorem posDef_schurSigma_of_blockPosDef {H : BlockMat d}
    (hsymm : IsSymmetricBlockMat H) (hpos : BlockPosDef H) :
    (schurSigma H).PosDef := by
  have hfull : (toFullBlockMat H).PosDef :=
    posDef_toFullBlockMat hsymm hpos
  have hstar : (schurSigmaStar H).PosDef :=
    (posDef_lowerRight hsymm hpos).inv
  have hform : toFullBlockMat H =
      schurBlock (schurSigma H) (schurSigmaStar H) (schurSkew H) :=
    Initialization.toFullBlockMat_eq_schurBlock hsymm hpos
  apply posDef_of_posDef_schurBlock hstar
  rwa [← hform]

/-- The drop of the hatted carrier controls the sum of the two normalized
Schur trace gaps.  The first gap measures the upper Schur block relative to
its coarse value, and the second measures the lower-right block relative to
its coarse value. -/
theorem schur_trace_gaps_le_hattedContrast_drop
    [NeZero d] {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F)
    (hCsharp : BlockMatLoewnerLE (blockSharp C) C) :
    Matrix.trace
          ((schurSigma F - schurSigma C) * (schurSigma C)⁻¹) +
        Matrix.trace
          ((F.lowerRight - C.lowerRight) * C.lowerRight⁻¹) ≤
      (d : ℝ) * (hattedContrast F - hattedContrast C) := by
  have hCright : C.lowerRight.PosDef := posDef_lowerRight hCsymm hCpos
  have hFright : F.lowerRight.PosDef := posDef_lowerRight hFsymm hFpos
  have hCsigma : (schurSigma C).PosDef :=
    posDef_schurSigma_of_blockPosDef hCsymm hCpos
  have hFsigma : (schurSigma F).PosDef :=
    posDef_schurSigma_of_blockPosDef hFsymm hFpos
  have hright : C.lowerRight ≤ F.lowerRight :=
    Initialization.le_of_matLoewnerLE hCright.isHermitian hFright.isHermitian
      (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hCF)
  have hsigma : schurSigma C ≤ schurSigma F := by
    apply Initialization.le_of_matLoewnerLE hCsigma.isHermitian hFsigma.isHermitian
    refine (matLoewnerLE_schurSigma_skewCorrectedForm
      hCpos (schurSkew F)).trans ?_
    have hfixed := matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE
      hCsymm hCpos hFsymm hFpos hCF (schurSkew F)
    simpa only [skewCorrectedForm, sub_self, Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero] using hfixed
  have hstarSigma : schurSigmaStar C ≤ schurSigma C :=
    Initialization.schurSigmaStar_le_schurSigma hCsymm hCpos hCsharp
  have hSigmaInvRight : (schurSigma C)⁻¹ ≤ F.lowerRight := by
    have hinv : (schurSigma C)⁻¹ ≤ (schurSigmaStar C)⁻¹ :=
      inv_le_inv_of_le (posDef_lowerRight hCsymm hCpos).inv hCsigma hstarSigma
    have hstarInv : (schurSigmaStar C)⁻¹ = C.lowerRight :=
      schurSigmaStar_inv C (isUnit_det_lowerRight hCpos)
    rw [hstarInv] at hinv
    exact hinv.trans hright
  have hfirst := PortableHistory.trace_mul_le_trace_mul
    (Matrix.le_iff.mp hsigma) hSigmaInvRight
  have hsecond := PortableHistory.trace_mul_le_trace_mul
    (Matrix.le_iff.mp hright) hstarSigma
  have hdecomp :
      Matrix.trace (F.lowerRight * schurSigma F) -
          Matrix.trace (C.lowerRight * schurSigma C) =
        Matrix.trace
            ((schurSigma F - schurSigma C) * F.lowerRight) +
          Matrix.trace
            ((F.lowerRight - C.lowerRight) * schurSigma C) := by
    simp only [Matrix.sub_mul, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm (schurSigma F) F.lowerRight,
      Matrix.trace_mul_comm (schurSigma C) F.lowerRight]
    ring
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  have hhat :
      (d : ℝ) * (hattedContrast F - hattedContrast C) =
        Matrix.trace (F.lowerRight * schurSigma F) -
          Matrix.trace (C.lowerRight * schurSigma C) := by
    rw [hattedContrast_eq_trace_lowerRight_mul hFsymm hFpos,
      hattedContrast_eq_trace_lowerRight_mul hCsymm hCpos]
    field_simp
  rw [hhat, hdecomp]
  have hsecond' :
      Matrix.trace
          ((F.lowerRight - C.lowerRight) * C.lowerRight⁻¹) ≤
        Matrix.trace
          ((F.lowerRight - C.lowerRight) * schurSigma C) := by
    simpa only [schurSigmaStar] using hsecond
  exact add_le_add hfirst hsecond'

private theorem trace_normalize_sub_one_eq_trace_sub_mul_inv
    {A B : Mat d} (hB : B.PosDef) :
    Matrix.trace (matSqrt B⁻¹ * A * matSqrt B⁻¹ - 1) =
      Matrix.trace ((A - B) * B⁻¹) := by
  have hdet : IsUnit B.det := isUnit_det_of_posDef hB
  have hnorm :
      Matrix.trace (matSqrt B⁻¹ * A * matSqrt B⁻¹) =
        Matrix.trace (B⁻¹ * A) := by
    calc
      Matrix.trace (matSqrt B⁻¹ * A * matSqrt B⁻¹) =
          Matrix.trace (matSqrt B⁻¹ * (matSqrt B⁻¹ * A)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((matSqrt B⁻¹ * matSqrt B⁻¹) * A) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace (B⁻¹ * A) := by
        rw [matSqrt_inv_mul_self hB]
  rw [Matrix.trace_sub, Matrix.trace_one, hnorm, Matrix.sub_mul,
    Matrix.trace_sub, Matrix.trace_mul_comm A B⁻¹,
    Matrix.mul_nonsing_inv B hdet, Matrix.trace_one]

/-- Operator-norm form of the two Schur scale gaps.  It is the first branch of
the good-quadratics estimate: both relative matrices lie above the identity,
so their spectral gaps are bounded by their trace gaps. -/
theorem normalized_schur_norm_gaps_le_hattedContrast_drop
    [NeZero d] {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F)
    (hCsharp : BlockMatLoewnerLE (blockSharp C) C) :
    ‖matSqrt (schurSigma C)⁻¹ * schurSigma F *
          matSqrt (schurSigma C)⁻¹ - 1‖ +
        ‖matSqrt C.lowerRight⁻¹ * F.lowerRight *
          matSqrt C.lowerRight⁻¹ - 1‖ ≤
      (d : ℝ) * (hattedContrast F - hattedContrast C) := by
  have : Nonempty (Fin d) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hCright : C.lowerRight.PosDef := posDef_lowerRight hCsymm hCpos
  have hFright : F.lowerRight.PosDef := posDef_lowerRight hFsymm hFpos
  have hCsigma : (schurSigma C).PosDef :=
    posDef_schurSigma_of_blockPosDef hCsymm hCpos
  have hFsigma : (schurSigma F).PosDef :=
    posDef_schurSigma_of_blockPosDef hFsymm hFpos
  have hright : C.lowerRight ≤ F.lowerRight :=
    Initialization.le_of_matLoewnerLE hCright.isHermitian hFright.isHermitian
      (matLoewnerLE_lowerRight_of_blockMatLoewnerLE hCF)
  have hsigma : schurSigma C ≤ schurSigma F := by
    apply Initialization.le_of_matLoewnerLE hCsigma.isHermitian hFsigma.isHermitian
    refine (matLoewnerLE_schurSigma_skewCorrectedForm
      hCpos (schurSkew F)).trans ?_
    have hfixed := matLoewnerLE_skewCorrectedForm_of_blockMatLoewnerLE
      hCsymm hCpos hFsymm hFpos hCF (schurSkew F)
    simpa only [skewCorrectedForm, sub_self, Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero] using hfixed
  let PS : Mat d := matSqrt (schurSigma C)⁻¹ * schurSigma F *
    matSqrt (schurSigma C)⁻¹
  let PR : Mat d := matSqrt C.lowerRight⁻¹ * F.lowerRight *
    matSqrt C.lowerRight⁻¹
  have hPSpos : PS.PosDef := posDef_normalize hFsigma hCsigma
  have hPRpos : PR.PosDef := posDef_normalize hFright hCright
  have honeS : (1 : Mat d) ≤ PS := Recurrence.one_le_normalize hCsigma hsigma
  have honeR : (1 : Mat d) ≤ PR := Recurrence.one_le_normalize hCright hright
  have hnormS : ‖PS - 1‖ ≤ Matrix.trace (PS - 1) := by
    rw [Response.norm_sub_one_eq_norm_sub_one hPSpos.posSemidef honeS]
    have htop := PortableHistory.norm_le_one_add_trace_sub_one hPSpos honeS
    linarith only [htop]
  have hnormR : ‖PR - 1‖ ≤ Matrix.trace (PR - 1) := by
    rw [Response.norm_sub_one_eq_norm_sub_one hPRpos.posSemidef honeR]
    have htop := PortableHistory.norm_le_one_add_trace_sub_one hPRpos honeR
    linarith only [htop]
  have htrace := schur_trace_gaps_le_hattedContrast_drop
    hCsymm hCpos hFsymm hFpos hCF hCsharp
  change ‖PS - 1‖ + ‖PR - 1‖ ≤ _
  calc
    ‖PS - 1‖ + ‖PR - 1‖ ≤
        Matrix.trace (PS - 1) + Matrix.trace (PR - 1) :=
      add_le_add hnormS hnormR
    _ = Matrix.trace
          ((schurSigma F - schurSigma C) * (schurSigma C)⁻¹) +
        Matrix.trace
          ((F.lowerRight - C.lowerRight) * C.lowerRight⁻¹) := by
      rw [show Matrix.trace (PS - 1) =
          Matrix.trace
            ((schurSigma F - schurSigma C) * (schurSigma C)⁻¹) by
        exact trace_normalize_sub_one_eq_trace_sub_mul_inv hCsigma,
        show Matrix.trace (PR - 1) =
          Matrix.trace
            ((F.lowerRight - C.lowerRight) * C.lowerRight⁻¹) by
        exact trace_normalize_sub_one_eq_trace_sub_mul_inv hCright]
    _ ≤ (d : ℝ) * (hattedContrast F - hattedContrast C) := htrace

/-- A common shear of two ordered Schur blocks gives the quadratic comparison
used to control the change of their Schur couplings. -/
theorem schurSkew_diff_shear_inequality
    {C F : BlockMat d}
    (hCsymm : IsSymmetricBlockMat C) (hCpos : BlockPosDef C)
    (hFsymm : IsSymmetricBlockMat F) (hFpos : BlockPosDef F)
    (hCF : BlockMatLoewnerLE C F) (eta : ℝ) :
    eta ^ (2 : ℕ) •
        ((schurSkew F - schurSkew C)ᴴ * C.lowerRight *
          (schurSkew F - schurSkew C)) ≤
      schurSigma F - schurSigma C +
        (1 - eta) ^ (2 : ℕ) •
          ((schurSkew F - schurSkew C)ᴴ * F.lowerRight *
            (schurSkew F - schurSkew C)) := by
  let D : Mat d := schurSkew F - schurSkew C
  let g : Mat d := schurSkew C + eta • D
  have hfull : toFullBlockMat C ≤ toFullBlockMat F :=
    (blockMatLoewnerLE_iff_le hCsymm hFsymm).mp hCF
  have hconj := conj_le_conj (fullBlockShear g) hfull
  rw [Initialization.toFullBlockMat_eq_schurBlock hCsymm hCpos,
    Initialization.toFullBlockMat_eq_schurBlock hFsymm hFpos,
    Response.schurBlock_conj_shear, Response.schurBlock_conj_shear] at hconj
  have htop := toBlocks₁₁_mono hconj
  rw [toBlocks₁₁_schurBlock, toBlocks₁₁_schurBlock,
    schurSigmaStar_inv C (isUnit_det_lowerRight hCpos),
    schurSigmaStar_inv F (isUnit_det_lowerRight hFpos)] at htop
  have hCdiff : schurSkew C - g = -(eta • D) := by
    simp only [g]
    abel
  have hFdiff : schurSkew F - g = (1 - eta) • D := by
    simp only [g, D]
    module
  rw [hCdiff, hFdiff] at htop
  have hleft :
      schurSigma C + (-(eta • D))ᴴ * C.lowerRight * (-(eta • D)) =
        schurSigma C + eta ^ (2 : ℕ) • (Dᴴ * C.lowerRight * D) := by
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
      star_trivial, neg_mul, mul_neg, neg_neg, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [pow_two]
  have hright :
      schurSigma F + ((1 - eta) • D)ᴴ * F.lowerRight * ((1 - eta) • D) =
        schurSigma F + (1 - eta) ^ (2 : ℕ) •
          (Dᴴ * F.lowerRight * D) := by
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    rw [pow_two]
  rw [hleft, hright] at htop
  change eta ^ (2 : ℕ) • (Dᴴ * C.lowerRight * D) ≤
    schurSigma F - schurSigma C +
      (1 - eta) ^ (2 : ℕ) • (Dᴴ * F.lowerRight * D)
  refine Matrix.le_iff.mpr ?_
  have hps := Matrix.le_iff.mp htop
  have hrw :
      schurSigma F - schurSigma C +
          (1 - eta) ^ (2 : ℕ) • (Dᴴ * F.lowerRight * D) -
        eta ^ (2 : ℕ) • (Dᴴ * C.lowerRight * D) =
      (schurSigma F +
          (1 - eta) ^ (2 : ℕ) • (Dᴴ * F.lowerRight * D)) -
        (schurSigma C + eta ^ (2 : ℕ) •
          (Dᴴ * C.lowerRight * D)) := by
    abel
  rwa [hrw]

end

end HCPolySupport.HighContrast.Quenched

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterCellRows

/-!
# High-contrast homogenization: Provider.Entry.AdapterCellMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed bound on an aligned adapted cell

Averaging the Euclidean filling of `z + ⋄_r^q` against the Euclidean cell bound
`E[𝐀(z+□_i)] ≤ (1+9K_{Ψ_S}^23^{-i})^g𝐄` and summing the geometric series gives
`E[𝐀(z+⋄_r^q)] ≤ C_d(1-g)^{-1}(1+9K_{Ψ_S}^23^{-r})^g𝐄` at every generation and
every aligned centre, with `C_d = 126d^{3/2}`.

This is the bound `e.coarse.ellipticity` does not give directly: the dagger
speaks of standard cubes, and an adapted cell is only reached through its own
Euclidean filling.  The single factor `(1-g)^{-1}` is the geometric series of
that filling; it is what the composed reading of the reverse comparison spends
over the printed boundary decomposition.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The annealed bound on an aligned adapted cell.**  Averaging the Euclidean
filling of `z + ⋄_r^q` against the Euclidean cell bound and summing the geometric
series gives `E[𝐀(z+⋄_r^q)] ≤ C_d(1-g)^{-1}(1+9K_{Ψ_S}^23^{-r})^g𝐄`, at every
generation and every aligned centre, with `C_d = 126d^{3/2}`.  The one factor
`(1-g)^{-1}` is the geometric series of the filling. -/
theorem annealedBlock_adaptedCellAt_le [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hd : 1 ≤ d) (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {q : Mat d} (hq : q.PosDef)
    (hqinv : ‖q⁻¹‖ ≤ 101 / 100) (r : ℤ) (w : Fin d → ℤ) :
    BlockMatLoewnerLE (annealedBlock P (adaptedCellAt q r w))
      (blockScale (126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹ *
        (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g) E) := by
  classical
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g < 1 := hdag.g_mem.2
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr hgpos.le
  have hinv1 : (1 : ℝ) ≤ (1 - g)⁻¹ := by
    rw [le_inv_comm₀ one_pos hgpos]
    linarith only [hg0]
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsqd : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1
  have hd32 : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt d := by nlinarith only [hd1, hsqd]
  obtain ⟨M, hM1, hMsub⟩ :=
    exists_containing_centeredCube hq r (adaptedCellCenter q r w)
  have hM0 : (0 : ℤ) ≤ M := by omega
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ :=
    Transport.maximal_filling hq hone r r (adaptedCellCenter q r w)
  have hnorm : ‖q⁻¹ * (1 : Mat d)‖ = ‖q⁻¹‖ := by rw [Matrix.mul_one]
  have hCd0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ := by positivity
  have hK1 : (1 : ℝ) < K := hdag.one_lt_growthWitness
  obtain ⟨J, hJ0, hJr, hJmul⟩ := exists_cutoff_mul_le hg1
    (2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ *
      (1 + (3 : ℝ) ^ M + 6 * K ^ 2))
    (show (0 : ℝ) < (3 : ℝ) ^ r by positivity) r
  have hmeas : HasMeasurableCoarseBlock P
      (adaptedCellTranslate q r (adaptedCellCenter q r w)) :=
    Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq r w
  have hW : HasIntegrableCoarseBlock P (adaptedCellTranslate q r (adaptedCellCenter q r w)) :=
    hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger hdag hq hmeas
  have hcellint : ∀ i ∈ Finset.Icc J r, ∀ v ∈ Z i,
      HasIntegrableCoarseBlock P (adaptedCellAt (1 : Mat d) i v) := by
    intro i _ v _
    rw [adaptedCellAt_one]
    exact hasIntegrableCoarseBlock_standardCell_of_stationary hstat hdag i v
  have hSint : Integrable S P := integrable_source hdag
  have haff : Integrable (fun a => (3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) P :=
    (integrable_const _).add (hSint.const_mul 3)
  have hGint : Integrable (fun a =>
      ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
          ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E) P := by
    have hscal : Integrable (fun a => (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
          ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) P :=
      ((haff.const_mul _).mul_const _).const_mul _
    have hGint' : Integrable (fun a : CoeffSpace d => fun α β : BlockCoord d =>
        ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
            ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) *
          toFullBlockMat E α β) P := by
      rw [integrable_pi_iff]
      intro α
      rw [integrable_pi_iff]
      intro β
      exact hscal.mul_const _
    exact hGint'
  have hkey := Transport.annealedBlock_le_of_ae_le hW hcellint hGint
    (ae_coarseBlock_adaptedCellTranslate_le_rows hdag hq hM0 hJr hMsub hZ)
  have hmeanS : ∫ a, S a ∂P ≤ 2 * K ^ 2 := integral_source_le hdag
  have hmean0 : (0 : ℝ) ≤ ∫ a, S a ∂P := integral_nonneg fun a => hdag.source_nonneg a
  have hGmean : ∫ a, ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
          ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E ∂P =
      ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
          ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E := by
    rw [integral_smul_const]
    congr 1
    have hcong : (fun a => (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
            ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) =
        fun a => ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (2 * (1 - g)⁻¹) *
              ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) *
              ((3 : ℝ) ^ J + (3 : ℝ) ^ M)) +
            ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (2 * (1 - g)⁻¹) *
              ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) * 3) * S a := by
      funext a
      ring
    rw [hcong, integral_affine hSint]
    ring
  rw [hGmean] at hkey
  intro X
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
    have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [star_trivial] at hx
    linarith only [hx]
  have hstep0 :
      blockVecDot X (blockMatVecMul
        (annealedBlock P (adaptedCellTranslate q r (adaptedCellCenter q r w))) X) ≤
        blockVecDot X (blockMatVecMul (ofFullBlockMat
          ((∑ i ∈ Finset.Icc J r, ∑ v ∈ Z i,
            ((volume (adaptedCellAt (1 : Mat d) i v)).toReal /
                (volume (adaptedCellTranslate q r (adaptedCellCenter q r w))).toReal) •
              toFullBlockMat (annealedBlock P (adaptedCellAt (1 : Mat d) i v))) +
            ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
              (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
                ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) •
              toFullBlockMat E)) X) := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, blockVecDot_blockMatVecMul_eq_dotProduct,
      toFullBlockMat_ofFullBlockMat]
    exact quad_le_of_le hkey _
  have hstep1 :
      1 / 2 * blockVecDot X (blockMatVecMul
        (annealedBlock P (adaptedCellTranslate q r (adaptedCellCenter q r w))) X) ≤
        1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat
          ((∑ i ∈ Finset.Icc J r, ∑ v ∈ Z i,
            ((volume (adaptedCellAt (1 : Mat d) i v)).toReal /
                (volume (adaptedCellTranslate q r (adaptedCellCenter q r w))).toReal) •
              toFullBlockMat (annealedBlock P (adaptedCellAt (1 : Mat d) i v))) +
            ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
              (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
                ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) •
              toFullBlockMat E)) X) := by linarith only [hstep0]
  rw [half_blockQuadratic_majorant] at hstep1
  -- the rows
  have hins : Finset.Icc J r = insert r (Finset.Ico J r) := (Finset.Ico_insert_right hJr).symm
  have hnotmem : r ∉ Finset.Ico J r := by simp
  rw [hins, Finset.sum_insert hnotmem] at hstep1
  have hrowtop : (∑ v ∈ Z r, (volume (adaptedCellAt (1 : Mat d) r v)).toReal /
        (volume (adaptedCellTranslate q r (adaptedCellCenter q r w))).toReal *
      (1 / 2 * blockVecDot X
        (blockMatVecMul (annealedBlock P (adaptedCellAt (1 : Mat d) r v)) X))) ≤
      1 * ((1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g *
        (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
    refine sum_weight_mul_le (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0) ?_
      (Transport.sum_relative_volume_row_le_one hq hone (hZ r))
    intro v _
    have hcell := annealedBlock_standardCell_le hstat hdag r v X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale, ← adaptedCellAt_one] at hcell
    linarith only [hcell]
  have h3rr : (3 : ℝ) ^ (r - r) = 1 := by rw [sub_self, zpow_zero]
  have hlow : (∑ i ∈ Finset.Ico J r, ∑ v ∈ Z i,
      (volume (adaptedCellAt (1 : Mat d) i v)).toReal /
          (volume (adaptedCellTranslate q r (adaptedCellCenter q r w))).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellAt (1 : Mat d) i v)) X))) ≤
      ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
        (20 * transferGauge g K r) := by
    have hb : ∀ i ∈ Finset.Ico J r,
        (∑ v ∈ Z i, (volume (adaptedCellAt (1 : Mat d) i v)).toReal /
            (volume (adaptedCellTranslate q r (adaptedCellCenter q r w))).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (annealedBlock P (adaptedCellAt (1 : Mat d) i v)) X))) ≤
          ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (i - r)) *
            ((1 + 9 * K ^ 2 * (3 : ℝ) ^ (-i)) ^ g *
              (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
      intro i hi
      refine sum_weight_mul_le (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0) ?_ ?_
      · intro v _
        have hcell := annealedBlock_standardCell_le hstat hdag i v X
        rw [Sharp.blockVecDot_blockMatVecMul_blockScale, ← adaptedCellAt_one] at hcell
        linarith only [hcell]
      · have hle := Transport.sum_relative_volume_row_le hq hone (Finset.mem_Ico.mp hi).2 (hZ i)
        rw [hnorm] at hle
        exact hle
    refine le_trans (Finset.sum_le_sum hb) ?_
    have hrw : ∀ i ∈ Finset.Ico J r,
        ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (i - r)) *
            ((1 + 9 * K ^ 2 * (3 : ℝ) ^ (-i)) ^ g *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)))
          = ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
              (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
            ((3 : ℝ) ^ (i - r) * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-i)) ^ g) :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    have hser := sum_belowSplit_le (K := K) hg0 hg1 r r J
    rw [h3rr, mul_one] at hser
    exact mul_le_mul_of_nonneg_left hser (mul_nonneg hCd0 hE0)
  -- the tail, under one unit
  have hchain : (3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P ≤
      1 + (3 : ℝ) ^ M + 6 * K ^ 2 := by
    have h3J : (3 : ℝ) ^ J ≤ 1 := by
      have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hJ0
      rwa [zpow_zero] at this
    linarith only [h3J, hmeanS]
  have hpowpos : (0 : ℝ) < (3 : ℝ) ^ ((J : ℝ) * (1 - g)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hAB : 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ *
      ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
      (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ (3 : ℝ) ^ r := by
    refine le_trans ?_ hJmul
    have h1 : (0 : ℝ) ≤ 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ :=
      mul_nonneg (by linarith only [hCd0]) hinv0
    have hmono := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hchain h1) hpowpos.le
    linarith only [hmono, hpowpos]
  have hcancel : (3 : ℝ) ^ (-r) * (3 : ℝ) ^ r = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  have htailfinal : (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
      (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
        ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))) ≤ 1 := by
    have h3r : (0 : ℝ) < (3 : ℝ) ^ (-r) := by positivity
    have hcal : (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
          ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))
        = (2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ *
            ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
            (3 : ℝ) ^ ((J : ℝ) * (1 - g))) * (3 : ℝ) ^ (-r) := by ring
    rw [hcal]
    have hmul := mul_le_mul_of_nonneg_right hAB h3r.le
    rw [mul_comm ((3 : ℝ) ^ r) ((3 : ℝ) ^ (-r))] at hmul
    linarith only [hmul, hcancel]
  -- the printed constant
  have hB1 : (1 : ℝ) ≤ (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g := by
    refine Real.one_le_rpow ?_ hg0
    have h1 : (0 : ℝ) ≤ 9 * K ^ 2 * (3 : ℝ) ^ (-r) := by positivity
    linarith only [h1]
  have hGamB : transferGauge g K r ≤ (1 - g)⁻¹ * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g := by
    rw [transferGauge]
    refine mul_le_mul_of_nonneg_left ?_ hinv0
    refine Real.rpow_le_rpow (by positivity) ?_ hg0
    have h1 : (0 : ℝ) < (3 : ℝ) ^ (-r) := by positivity
    have hK2 : (1 : ℝ) ≤ K ^ 2 := by nlinarith only [hK1]
    nlinarith only [h1, hK2]
  have hGam0 : (0 : ℝ) ≤ transferGauge g K r := by
    have hbase : (0 : ℝ) ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-r)) ^ g :=
      Real.rpow_nonneg (by positivity) g
    rw [transferGauge]
    exact mul_nonneg hinv0 hbase
  have hCdub : 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ ≤ 6 * (d : ℝ) * Real.sqrt d * (101 / 100) :=
    mul_le_mul_of_nonneg_left hqinv (by positivity)
  have hstepP : (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (20 * transferGauge g K r) ≤
      (6 * (d : ℝ) * Real.sqrt d * (101 / 100)) *
        (20 * ((1 - g)⁻¹ * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g)) := by
    refine mul_le_mul hCdub (mul_le_mul_of_nonneg_left hGamB (by norm_num)) ?_ ?_
    · linarith only [hGam0]
    · positivity
  have hp1 : (1 - g)⁻¹ * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g ≥
      (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g := by nlinarith only [hinv1, hB1]
  have hp2 : (d : ℝ) * Real.sqrt d * ((1 - g)⁻¹ * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g) ≥
      (1 - g)⁻¹ * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g := by
    nlinarith only [hd32, hp1, hB1]
  have hcoef : (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g +
      (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (20 * transferGauge g K r) +
      (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
          ((3 : ℝ) ^ (-r) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))) ≤
      126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹ * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g := by
    linarith only [hstepP, htailfinal, hp1, hp2, hB1]
  have hmulcoef := mul_le_mul_of_nonneg_right hcoef hE0
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hgoal : adaptedCellAt q r w = adaptedCellTranslate q r (adaptedCellCenter q r w) := rfl
  rw [hgoal]
  linarith only [hstep1, hrowtop, hlow, hmulcoef]

end

end Entry
end HighContrast
end HCPolySupport

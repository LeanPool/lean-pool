/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterReverseRows

/-!
# High-contrast homogenization: Provider.Entry.AdapterReverse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reverse half of the adapted-to-Euclidean comparison

The second estimate of the comparison between adapted and Euclidean cubes:

`F_m - E_n^q ≤ C𝔢_qΓ_{g,S}(n)3^{-(m-n)}𝐄`  for `ℓ_al ≤ n < m`.

The starting row of the adapted filling of `□_m` consists of integer translates
of `⋄_n^q`, so each of its cells has annealed block exactly `E_n^q` and the rows
together carry relative volume at most one.  Below the starting scale a cell is
an adapted cell of a lower generation, which `e.coarse.ellipticity` does not
bound directly; `Entry.annealedBlock_adaptedCellAt_le` bounds it through its own
Euclidean filling, and the cross-grid row weight `C_d|q|3^{r-m}` against that
bound is summed by `Entry.sum_belowSplit_le` at the printed rate
`20Γ_{g,S}(n)3^{-(m-n)}`.

The constant exhibited carries the extra `(1-g)^{-1}` of that composed reading.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem adaptedLowRows_energy_le [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hd : 1 ≤ d)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {q : Mat d} (hq : q.PosDef) (hqinv : ‖q⁻¹‖ ≤ 101 / 100)
    {n m J : ℤ} (hg0 : 0 ≤ g) (hg1 : g < 1)
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = Transport.fillingIndex q n
      (adaptedCellTranslate (1 : Mat d) m 0) r)
    (X : BlockVec d)
    (hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X)) :
    (∑ r ∈ Finset.Ico J n, ∑ w ∈ Z r,
      (volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal *
        (1 / 2 * blockVecDot X (blockMatVecMul (annealedBlock P (adaptedCellAt q r w)) X))) ≤
      ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) * (126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹) *
          (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
        (20 * transferGauge g K n * (3 : ℝ) ^ (n - m)) := by
  have hCq0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q‖ := by positivity
  have hnorm : ‖(1 : Mat d)⁻¹ * q‖ = ‖q‖ := by rw [inv_one, Matrix.one_mul]
  have hb : ∀ r ∈ Finset.Ico J n,
      (∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellAt q r w)) X))) ≤
        ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) * (3 : ℝ) ^ (r - m)) *
          ((126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹ *
              (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g) *
            (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
    intro r hr
    refine sum_weight_mul_le ?_ ?_ ?_
    · refine mul_nonneg ?_ hE0
      have h1 : (0 : ℝ) ≤ (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g :=
        Real.rpow_nonneg (by positivity) g
      have h2 : (0 : ℝ) ≤ 126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹ := by positivity
      exact mul_nonneg h2 h1
    · intro w _
      have hcell := annealedBlock_adaptedCellAt_le hd hstat hdag hq hqinv r w X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
      linarith only [hcell]
    · have hle := Transport.sum_relative_volume_row_le Matrix.PosDef.one hq
        (Finset.mem_Ico.mp hr).2 (hZ r)
      rw [hnorm] at hle
      exact hle
  refine le_trans (Finset.sum_le_sum hb) ?_
  have hrw : ∀ r ∈ Finset.Ico J n,
      ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) * (3 : ℝ) ^ (r - m)) *
          ((126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹ *
              (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g) *
            (1 / 2 * blockVecDot X (blockMatVecMul E X))) =
        ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
            (126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹) *
            (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
          ((3 : ℝ) ^ (r - m) * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g) :=
    fun r _ => by ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (sum_belowSplit_le hg0 hg1 n m J) ?_
  have h2 : (0 : ℝ) ≤ 126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹ := by positivity
  exact mul_nonneg (mul_nonneg hCq0 h2) hE0

private theorem reverseCutoffTail_le {g K : ℝ} {n m J : ℤ}
    (hg1 : g < 1) (hJ0 : J ≤ 0)
    (hGam1 : 1 ≤ transferGauge g K n)
    {A B T : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hT : T ≤ 2 * K ^ 2)
    (hJmul : A * B * (1 + (3 : ℝ) ^ m + 6 * K ^ 2) *
      (2 * (1 - g)⁻¹) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ (3 : ℝ) ^ n) :
    A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * T) *
      (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) ≤
      transferGauge g K n * (3 : ℝ) ^ (n - m) := by
  have hchain : (3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * T ≤
      1 + (3 : ℝ) ^ m + 6 * K ^ 2 := by
    have h3J : (3 : ℝ) ^ J ≤ 1 := by
      have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hJ0
      rwa [zpow_zero] at this
    linarith only [h3J, hT]
  have hpowpos : (0 : ℝ) < (3 : ℝ) ^ ((J : ℝ) * (1 - g)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hAB : A * B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * T) *
      (2 * (1 - g)⁻¹) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ (3 : ℝ) ^ n := by
    refine le_trans ?_ hJmul
    have h1 : (0 : ℝ) ≤ A * B := mul_nonneg hA0 hB0
    have h2 : (0 : ℝ) ≤ 2 * (1 - g)⁻¹ := by positivity
    have hmono := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hchain h1) h2) hpowpos.le
    linarith only [hmono, hpowpos]
  have h3m : (0 : ℝ) < (3 : ℝ) ^ (-m) := by positivity
  have h3nm : (3 : ℝ) ^ (-m) * (3 : ℝ) ^ n = (3 : ℝ) ^ (n - m) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have h3nmpos : (0 : ℝ) < (3 : ℝ) ^ (n - m) := by positivity
  have hcal : A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * T) *
      (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) =
      (A * B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * T) *
        (2 * (1 - g)⁻¹) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) * (3 : ℝ) ^ (-m) := by
    ring
  rw [hcal]
  have hmul := mul_le_mul_of_nonneg_right hAB h3m.le
  rw [mul_comm ((3 : ℝ) ^ n) ((3 : ℝ) ^ (-m)), h3nm] at hmul
  nlinarith only [hmul, hGam1, h3nmpos]

private theorem integrable_affine_fullBlock {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {S : CoeffSpace d → ℝ} {J m : ℤ}
    {A B D : ℝ} (hSint : Integrable S P) (E : BlockMat d) :
    Integrable (fun a =>
      (A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) * D)) • toFullBlockMat E) P ∧
    (∫ a, (A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) * D)) •
        toFullBlockMat E ∂P) =
      (A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * ∫ a, S a ∂P) * D)) •
        toFullBlockMat E := by
  have haff : Integrable (fun a => (3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) P :=
    (integrable_const _).add (hSint.const_mul 3)
  have hscal : Integrable (fun a =>
      A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) * D)) P :=
    (((haff.const_mul B).mul_const D).const_mul A)
  have hfull : Integrable (fun a : CoeffSpace d => fun α β : BlockCoord d =>
      (A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) * D)) *
        toFullBlockMat E α β) P := by
    rw [integrable_pi_iff]
    intro α
    rw [integrable_pi_iff]
    intro β
    exact hscal.mul_const _
  refine ⟨hfull, ?_⟩
  rw [integral_smul_const]
  congr 1
  have hcong : (fun a => A * (B * ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) * D)) =
      fun a => (A * B * D * ((3 : ℝ) ^ J + (3 : ℝ) ^ m)) +
        (A * B * D * 3) * S a := by
    funext a
    ring
  rw [hcong, integral_affine hSint]
  ring

/-- **The reverse half of the adapted-to-Euclidean comparison.**  For
`ℓ_al ≤ n < m` the Euclidean mean at generation `m` exceeds the adapted mean at
generation `n` by at most `C𝔢_qΓ_{g,S}(n)3^{-(m-n)}𝐄`.  The constant exhibited
here carries the extra `(1-g)^{-1}` of the composed reading of the boundary
cells; the printed constant is dimension-only, and reaching it would need the
boundary shell of the printed decomposition rather than the composed filling. -/
theorem centeredCube_sub_adaptedMean_le [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hd : 1 ≤ d) (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {lAl : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid lAl q) (hqinv : ‖q⁻¹‖ ≤ 101 / 100) {n m : ℤ}
    (hlAl : lAl ≤ n) (hn : 0 ≤ n) (hnm : n < m) :
    BlockMatLoewnerLE
      (blockSub (annealedBlock P (centeredCube d m)) (adaptedMean P q n))
      (blockScale ((15120 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * ‖q‖ + 1) *
        transferGauge g K n * (3 : ℝ) ^ (n - m)) E) := by
  classical
  have hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g < 1 := hdag.g_mem.2
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr hgpos.le
  have hinv1 : (1 : ℝ) ≤ (1 - g)⁻¹ := by
    rw [le_inv_comm₀ one_pos hgpos]
    linarith only [hg0]
  have hm0 : (0 : ℤ) ≤ m := by omega
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsq : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt (by positivity)
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have htarget : adaptedCellTranslate (1 : Mat d) m 0 = centeredCube d m :=
    adaptedCellTranslate_one_zero m
  have hnorm : ‖(1 : Mat d)⁻¹ * q‖ = ‖q‖ := by rw [inv_one, Matrix.one_mul]
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ := Transport.maximal_filling hone hq n m (0 : Vec d)
  have hCq0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q‖ := by positivity
  have hB0 : (0 : ℝ) ≤ 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1 := by
    have h1 : (0 : ℝ) ≤ 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) := by positivity
    have := mul_nonneg h1 hinv0
    linarith only [this]
  have hK1 : (1 : ℝ) < K := hdag.one_lt_growthWitness
  obtain ⟨J, hJ0, hJn, hJmul⟩ := exists_cutoff_mul_le hg1
    ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
      (2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
      (1 + (3 : ℝ) ^ m + 6 * K ^ 2) * (2 * (1 - g)⁻¹))
    (show (0 : ℝ) < (3 : ℝ) ^ n by positivity) n
  -- the averaged exhaustion at the chosen cutoff
  have hW : HasIntegrableCoarseBlock P (adaptedCellTranslate (1 : Mat d) m 0) := by
    rw [htarget]
    exact hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag m
  have hcellint : ∀ r ∈ Finset.Icc J n, ∀ w ∈ Z r,
      HasIntegrableCoarseBlock P (adaptedCellAt q r w) := by
    intro r _ w _
    exact hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger (y := adaptedCellCenter q r w)
      hdag hq (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq r w)
  have hSint : Integrable S P := integrable_source hdag
  have haff : Integrable (fun a => (3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) P :=
    (integrable_const _).add (hSint.const_mul 3)
  obtain ⟨hGint, hGmean⟩ := integrable_affine_fullBlock hSint E
    (A := 6 * (d : ℝ) * Real.sqrt d * ‖q‖)
    (B := 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1)
    (D := 2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))
  have hkey := Transport.annealedBlock_le_of_ae_le hW hcellint hGint
    (ae_coarseBlock_centeredCube_le_rows hdag hq hm0 hJn hZ)
  have hmeanS : ∫ a, S a ∂P ≤ 2 * K ^ 2 := integral_source_le hdag
  rw [hGmean] at hkey
  rw [← htarget]
  intro X
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
    have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [star_trivial] at hx
    linarith only [hx]
  have hfinq : HasFiniteAdaptedMean P q n := by
    have hWeq : adaptedCellTranslate q n 0 = adaptedCell q n := by simp [adaptedCellTranslate]
    have hmeasq : HasMeasurableCoarseBlock P (adaptedCellTranslate q n 0) := by
      rw [hWeq]
      exact Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq n
    have h := hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger hdag hq hmeasq
    rw [hWeq] at h
    exact h
  have hEnpd : (toFullBlockMat (adaptedMean P q n)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q n)
      (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid n hfinq)
  have hEn0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul (adaptedMean P q n) X) := by
    have hx := hEnpd.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [star_trivial] at hx
    linarith only [hx]
  have hstep0 :
      blockVecDot X (blockMatVecMul
        (annealedBlock P (adaptedCellTranslate (1 : Mat d) m 0)) X) ≤
        blockVecDot X (blockMatVecMul (ofFullBlockMat
          ((∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            ((volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal) •
              toFullBlockMat (annealedBlock P (adaptedCellAt q r w))) +
            ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
              ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
                ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * ∫ a, S a ∂P) *
                (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))))) •
              toFullBlockMat E)) X) := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, blockVecDot_blockMatVecMul_eq_dotProduct,
      toFullBlockMat_ofFullBlockMat]
    exact quad_le_of_le hkey _
  have hstep1 :
      1 / 2 * blockVecDot X (blockMatVecMul
        (annealedBlock P (adaptedCellTranslate (1 : Mat d) m 0)) X) ≤
        1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat
          ((∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            ((volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal) •
              toFullBlockMat (annealedBlock P (adaptedCellAt q r w))) +
            ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
              ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
                ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * ∫ a, S a ∂P) *
                (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))))) •
              toFullBlockMat E)) X) := by linarith only [hstep0]
  rw [half_blockQuadratic_majorant] at hstep1
  have hins : Finset.Icc J n = insert n (Finset.Ico J n) := (Finset.Ico_insert_right hJn).symm
  have hnotmem : n ∉ Finset.Ico J n := by simp
  rw [hins, Finset.sum_insert hnotmem] at hstep1
  -- the starting row: every cell has the adapted mean as its annealed block
  have hmeasn : HasMeasurableCoarseBlock P (adaptedCell q n) :=
    Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq n
  have hrowtop : (∑ w ∈ Z n, (volume (adaptedCellAt q n w)).toReal /
        (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal *
      (1 / 2 * blockVecDot X
        (blockMatVecMul (annealedBlock P (adaptedCellAt q n w)) X))) ≤
      1 * (1 / 2 * blockVecDot X (blockMatVecMul (adaptedMean P q n) X)) := by
    refine sum_weight_mul_le hEn0 ?_ (Transport.sum_relative_volume_row_le_one hone hq (hZ n))
    intro w _
    rw [Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hstat hgrid hlAl hmeasn w]
  -- the rows below the starting generation
  have hlow := adaptedLowRows_energy_le (J := J) hd hstat hdag hq hqinv hg0 hg1 hZ X hE0
  -- the tail, under one unit of the printed error
  have hGam1 : (1 : ℝ) ≤ transferGauge g K n := one_le_transferGauge hg0 hg1 n
  have h3nm : (3 : ℝ) ^ (-m) * (3 : ℝ) ^ n = (3 : ℝ) ^ (n - m) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have h3nmpos : (0 : ℝ) < (3 : ℝ) ^ (n - m) := by positivity
  have htailfinal := reverseCutoffTail_le hg1 hJ0 hGam1
    (A := 6 * (d : ℝ) * Real.sqrt d * ‖q‖)
    (B := 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1)
    (T := ∫ a, S a ∂P) (by positivity) (by positivity) hmeanS hJmul
  have hGam0 : (0 : ℝ) ≤ transferGauge g K n * (3 : ℝ) ^ (n - m) := by
    nlinarith only [hGam1, h3nmpos]
  have hCdub : (6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
      (126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹) =
      756 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * ‖q‖ := by
    linear_combination (756 * ‖q‖ * (1 - g)⁻¹ * (d : ℝ) ^ 2) * hsq
  have hP1 : ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
        (126 * (d : ℝ) * Real.sqrt d * (1 - g)⁻¹) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
      (20 * transferGauge g K n * (3 : ℝ) ^ (n - m)) =
      (15120 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * ‖q‖) *
        (transferGauge g K n * (3 : ℝ) ^ (n - m)) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X)) := by
    rw [hCdub]
    ring
  have hP2 : ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
        ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
          ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * ∫ a, S a ∂P) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))))) *
      (1 / 2 * blockVecDot X (blockMatVecMul E X)) ≤
      (transferGauge g K n * (3 : ℝ) ^ (n - m)) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X)) :=
    mul_le_mul_of_nonneg_right htailfinal hE0
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hsubq : blockVecDot X (blockMatVecMul
      (blockSub (annealedBlock P (adaptedCellTranslate (1 : Mat d) m 0))
        (adaptedMean P q n)) X)
      = blockVecDot X (blockMatVecMul
          (annealedBlock P (adaptedCellTranslate (1 : Mat d) m 0)) X) -
        blockVecDot X (blockMatVecMul (adaptedMean P q n) X) := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, blockVecDot_blockMatVecMul_eq_dotProduct,
      blockVecDot_blockMatVecMul_eq_dotProduct, Recurrence.toFullBlockMat_blockSub,
      Matrix.sub_mulVec, dotProduct_sub]
  rw [hsubq]
  linarith only [hstep1, hrowtop, hlow, hP1, hP2]

end

end Entry
end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterCellMean

/-!
# High-contrast homogenization: Provider.Entry.AdapterForward

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The forward half of the adapted-to-Euclidean comparison

The first estimate of the comparison between adapted and Euclidean cubes:

`E_n^q - F_k ≤ C_AE(d)𝔢_qΓ_{g,S}(k)3^{-(n-k)}𝐄`  for `0 ≤ k < n`.

The adapted cell `⋄_n^q` is filled by the Euclidean cells and the rows split at
the comparison generation.  A row at or above it is paid by the annealed mean
order on the Euclidean cubes — every cube of a generation `r ≥ k` has annealed
block below `F_k`, and the rows together carry relative volume at most one.  A
row below it is paid by the Euclidean cell bound
`E[𝐀(z+□_r)] ≤ (1+9K_{Ψ_S}^23^{-r})^g𝐄` against the cross-grid row weight
`C_d|q^{-1}|3^{r-n}`, and the geometric series `Entry.sum_belowSplit_le` totals
them at the printed `20Γ_{g,S}(k)3^{-(n-k)}`.

Only finitely many rows can be averaged at once, so the rows below an explicitly
chosen cutoff are kept pathwise, in the crude majorant of `AdapterMajorant`; the
cutoff is chosen so that the mean of that tail is under one fifth of a unit of
the printed error.  No limit is taken: the exhaustion of
`e.two.grid.whitney.average` already contains the passage to the limit, and
what is fed to it is a majorant of every finite partial sum.

The exhibited constant of this half is the printed one, `122d^{3/2}`; the
cross-grid factor `|q^{-1}| ≤ 101/100` carries no eccentricity.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem cutoffBudget {d : ℕ} {g K c T : ℝ} {k J M : ℤ}
    (hg1 : g < 1) (hJ0 : J ≤ 0) (hmean : T ≤ 2 * K ^ 2)
    (hJmul : 2 * c * (1 + (3 : ℝ) ^ M + 6 * K ^ 2) *
      (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ 4 / 5 * (3 : ℝ) ^ k) :
    2 * c * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * T) *
      (3 : ℝ) ^ ((J : ℝ) * (1 - g)) ≤ 4 / 5 * (3 : ℝ) ^ k := by
  have hchain : (3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * T ≤
      1 + (3 : ℝ) ^ M + 6 * K ^ 2 := by
    have h3J : (3 : ℝ) ^ J ≤ 1 := by
      have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hJ0
      rwa [zpow_zero] at this
    linarith only [h3J, hmean]
  have hpowpos : (0 : ℝ) < (3 : ℝ) ^ ((J : ℝ) * (1 - g)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine le_trans ?_ hJmul
  have h1 : (0 : ℝ) ≤ 2 * c := by positivity
  have hmono := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hchain h1) hpowpos.le
  linarith only [hmono, hpowpos]

private theorem forwardRowsBounds [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {q : Mat d}
    (hq : q.PosDef) {k n J : ℤ} (hk : 0 ≤ k) (hkn : k < n)
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = fillingIndex (1 : Mat d) n (adaptedCellTranslate q n 0) r)
    (X : BlockVec d)
    (hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X))
    (hF0 : 0 ≤ 1 / 2 * blockVecDot X
      (blockMatVecMul (annealedBlock P (centeredCube d k)) X)) :
    ((∑ r ∈ Finset.Icc k n, ∑ w ∈ Z r,
      (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
          (volume (adaptedCellTranslate q n 0)).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellAt (1 : Mat d) r w)) X))) ≤
      1 / 2 * blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d k)) X)) ∧
    ((∑ r ∈ Finset.Ico J k, ∑ w ∈ Z r,
      (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
          (volume (adaptedCellTranslate q n 0)).toReal *
        (1 / 2 * blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellAt (1 : Mat d) r w)) X))) ≤
      ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
        (20 * transferGauge g K k * (3 : ℝ) ^ (k - n))) := by
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have hnorm : ‖q⁻¹ * (1 : Mat d)‖ = ‖q⁻¹‖ := by rw [Matrix.mul_one]
  have hCd0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ := by positivity
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g < 1 := hdag.g_mem.2
  constructor
  · have hb : ∀ r ∈ Finset.Icc k n,
        (∑ w ∈ Z r, (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q n 0)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (annealedBlock P (adaptedCellAt (1 : Mat d) r w)) X))) ≤
          (∑ w ∈ Z r, (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q n 0)).toReal) *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (annealedBlock P (centeredCube d k)) X)) := by
      intro r hr
      refine sum_weight_mul_le hF0 ?_ le_rfl
      intro w _
      have hcell := annealedBlock_standardCell_le_centeredCube hstat hdag hk
        (Finset.mem_Icc.mp hr).1 w X
      rw [← adaptedCellAt_one] at hcell
      linarith only [hcell]
    refine le_trans (Finset.sum_le_sum hb) ?_
    rw [← Finset.sum_mul]
    have hm := Transport.sum_relative_volume_le_one hq hone (R := Finset.Icc k n) hZ
    have hmul := mul_le_mul_of_nonneg_right hm hF0
    linarith only [hmul]
      -- the rows below the comparison generation
  · have hb : ∀ r ∈ Finset.Ico J k,
        (∑ w ∈ Z r, (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q n 0)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (annealedBlock P (adaptedCellAt (1 : Mat d) r w)) X))) ≤
          ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (r - n)) *
            ((1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g *
              (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
      intro r hr
      have hrn : r < n := lt_of_lt_of_le (Finset.mem_Ico.mp hr).2 (le_of_lt hkn)
      refine sum_weight_mul_le (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0) ?_ ?_
      · intro w _
        have hcell := annealedBlock_standardCell_le hstat hdag r w X
        rw [Sharp.blockVecDot_blockMatVecMul_blockScale, ← adaptedCellAt_one] at hcell
        linarith only [hcell]
      · have hle := Transport.sum_relative_volume_row_le hq hone hrn (hZ r)
        rw [hnorm] at hle
        exact hle
    refine le_trans (Finset.sum_le_sum hb) ?_
    have hrw : ∀ r ∈ Finset.Ico J k,
        ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (r - n)) *
            ((1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)))
          = ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
              (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
            ((3 : ℝ) ^ (r - n) * (1 + 9 * K ^ 2 * (3 : ℝ) ^ (-r)) ^ g) :=
      fun r _ => by ring
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_belowSplit_le hg0 hg1 k n J) (mul_nonneg hCd0 hE0)

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


private theorem cutoffTailBound {d : ℕ} {g K a c b : ℝ} {k n : ℤ}
    (hg1 : g < 1) (hd32 : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt d)
    (hgam1 : 1 ≤ transferGauge g K k)
    (hcut : 2 * c * a * b ≤ 4 / 5 * (3 : ℝ) ^ k)
    (hinvGam : (1 - g)⁻¹ ≤ transferGauge g K k)
    (h3kn : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ k = (3 : ℝ) ^ (k - n)) :
    c * (2 * (1 - g)⁻¹ * a * ((3 : ℝ) ^ (-n) * b)) ≤
      4 / 5 * ((d : ℝ) * Real.sqrt d) * transferGauge g K k *
        (3 : ℝ) ^ (k - n) := by
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hg1).le
  have hrest : (0 : ℝ) ≤ (1 - g)⁻¹ * (3 : ℝ) ^ (-n) :=
    mul_nonneg hinv0 (by positivity)
  have hcal : c * (2 * (1 - g)⁻¹ * a * ((3 : ℝ) ^ (-n) * b)) =
      (2 * c * a * b) * ((1 - g)⁻¹ * (3 : ℝ) ^ (-n)) := by ring
  rw [hcal]
  refine le_trans (mul_le_mul_of_nonneg_right hcut hrest) ?_
  have hstep : 4 / 5 * (3 : ℝ) ^ k * ((1 - g)⁻¹ * (3 : ℝ) ^ (-n)) =
      (1 - g)⁻¹ * (4 / 5 * (3 : ℝ) ^ (k - n)) := by
    rw [← h3kn]
    ring
  rw [hstep]
  have h45 : (0 : ℝ) ≤ 4 / 5 * (3 : ℝ) ^ (k - n) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hinvGam h45
  have hgampos : (0 : ℝ) ≤ transferGauge g K k * (3 : ℝ) ^ (k - n) :=
    mul_nonneg hgam1.le (by positivity)
  have h2 : transferGauge g K k * (4 / 5 * (3 : ℝ) ^ (k - n)) ≤
      4 / 5 * ((d : ℝ) * Real.sqrt d) * transferGauge g K k *
        (3 : ℝ) ^ (k - n) := by
    nlinarith only [hd32, hgampos]
  linarith only [h1, h2]

/-- **The forward half of the adapted-to-Euclidean comparison.**  For
`0 ≤ k < n` the adapted mean at generation `n` exceeds the Euclidean mean at
generation `k` by at most `C_AE(d)Γ_{g,S}(k)3^{-(n-k)}𝐄`, with the exhibited
constant `C_AE(d) = 122d^{3/2}`; the cross-grid factor is `|q^{-1}| ≤ 101/100`
and carries no eccentricity. -/
theorem adaptedMean_sub_centeredCube_le [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hd : 1 ≤ d) (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {q : Mat d} (hq : q.PosDef)
    (hqinv : ‖q⁻¹‖ ≤ 101 / 100) {k n : ℤ} (hk : 0 ≤ k) (hkn : k < n) :
    BlockMatLoewnerLE
      (blockSub (annealedBlock P (adaptedCell q n)) (annealedBlock P (centeredCube d k)))
      (blockScale (122 * (d : ℝ) * Real.sqrt d * transferGauge g K k *
        (3 : ℝ) ^ (k - n)) E) := by
  classical
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g < 1 := hdag.g_mem.2
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr hgpos.le
  have hn0 : (0 : ℤ) ≤ n := by omega
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsqd : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1
  have hd32 : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt d := by nlinarith only [hd1, hsqd]
  obtain ⟨M, hM1, hMsub⟩ := exists_containing_centeredCube hq n (0 : Vec d)
  have hM0 : (0 : ℤ) ≤ M := by omega
  have hWeq : adaptedCellTranslate q n 0 = adaptedCell q n := by simp [adaptedCellTranslate]
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  obtain ⟨Z, hZ, -, -, -, -, -, -, -⟩ := Transport.maximal_filling hq hone n n (0 : Vec d)
  have hnorm : ‖q⁻¹ * (1 : Mat d)‖ = ‖q⁻¹‖ := by rw [Matrix.mul_one]
  have hCd0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ := by positivity
  have hK1 : (1 : ℝ) < K := hdag.one_lt_growthWitness
  obtain ⟨J, hJ0, hJk, hJmul⟩ := exists_cutoff_mul_le hg1
    (2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 + (3 : ℝ) ^ M + 6 * K ^ 2))
    (show (0 : ℝ) < 4 / 5 * (3 : ℝ) ^ k by positivity) k
  have hJn : J ≤ n := le_trans hJk (le_of_lt hkn)
  -- the averaged exhaustion at the chosen cutoff
  have hmeas : HasMeasurableCoarseBlock P (adaptedCellTranslate q n 0) := by
    rw [hWeq]
    exact Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq n
  have hW : HasIntegrableCoarseBlock P (adaptedCellTranslate q n 0) :=
    hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger hdag hq hmeas
  have hcellint : ∀ r ∈ Finset.Icc J n, ∀ w ∈ Z r,
      HasIntegrableCoarseBlock P (adaptedCellAt (1 : Mat d) r w) := by
    intro r _ w _
    rw [adaptedCellAt_one]
    exact hasIntegrableCoarseBlock_standardCell_of_stationary hstat hdag r w
  have hSint : Integrable S P := integrable_source hdag
  obtain ⟨hGint', hGmean'⟩ := integrable_affine_fullBlock hSint E
    (A := 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖)
    (B := 2 * (1 - g)⁻¹)
    (D := (3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))
  have hGint : Integrable (fun a =>
      ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
          ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E) P := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hGint'
  have hkey := Transport.annealedBlock_le_of_ae_le hW hcellint hGint
    (ae_coarseBlock_adaptedCellTranslate_le_rows hdag hq hM0 hJn hMsub hZ)
  -- the mean of the tail, in closed form
  have hmeanS : ∫ a, S a ∂P ≤ 2 * K ^ 2 := integral_source_le hdag
  have hmean0 : (0 : ℝ) ≤ ∫ a, S a ∂P := integral_nonneg fun a => hdag.source_nonneg a
  have hGmean : ∫ a, ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
          ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E ∂P =
      ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
          ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hGmean'
  rw [hGmean] at hkey
  -- the two orders on the rows
  rw [← hWeq]
  intro X
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
    have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [star_trivial] at hx
    linarith only [hx]
  have hFpd : (toFullBlockMat (annealedBlock P (centeredCube d k))).PosDef :=
    posDef_toFullBlockMat (isSymmetricBlockMat_annealedBlock P _)
      (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag k)
  have hF0 : 0 ≤ 1 / 2 *
      blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d k)) X) := by
    have hx := hFpd.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [star_trivial] at hx
    linarith only [hx]
  have hstep0 :
      blockVecDot X (blockMatVecMul (annealedBlock P (adaptedCellTranslate q n 0)) X) ≤
        blockVecDot X (blockMatVecMul (ofFullBlockMat
          ((∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            ((volume (adaptedCellAt (1 : Mat d) r w)).toReal /
                (volume (adaptedCellTranslate q n 0)).toReal) •
              toFullBlockMat (annealedBlock P (adaptedCellAt (1 : Mat d) r w))) +
            ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
              (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
                ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) •
              toFullBlockMat E)) X) := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, blockVecDot_blockMatVecMul_eq_dotProduct,
      toFullBlockMat_ofFullBlockMat]
    exact quad_le_of_le hkey _
  have hstep1 :
      1 / 2 * blockVecDot X
          (blockMatVecMul (annealedBlock P (adaptedCellTranslate q n 0)) X) ≤
        1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat
          ((∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            ((volume (adaptedCellAt (1 : Mat d) r w)).toReal /
                (volume (adaptedCellTranslate q n 0)).toReal) •
              toFullBlockMat (annealedBlock P (adaptedCellAt (1 : Mat d) r w))) +
            ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
              (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
                ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) •
              toFullBlockMat E)) X) := by linarith only [hstep0]
  rw [half_blockQuadratic_majorant] at hstep1
  -- the split of the rows at the comparison generation
  have hdisj : Disjoint (Finset.Ico J k) (Finset.Icc k n) := by
    refine Finset.disjoint_left.mpr fun i hi hi' => ?_
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_Icc] at hi'
    omega
  have hsplit : Finset.Icc J n = Finset.Ico J k ∪ Finset.Icc k n := by
    show Finset.Ico J (n + 1) = Finset.Ico J k ∪ Finset.Ico k (n + 1)
    exact (Finset.Ico_union_Ico_eq_Ico hJk (by omega)).symm
  rw [hsplit, Finset.sum_union hdisj] at hstep1
  -- the rows at or above the comparison generation
  obtain ⟨hhigh, hlow⟩ := forwardRowsBounds hstat hdag hq hk hkn hZ X hE0 hF0
  -- the tail, under one unit of the printed error
  have hGam1 : (1 : ℝ) ≤ transferGauge g K k := one_le_transferGauge hg0 hg1 k
  have hinvGam : (1 - g)⁻¹ ≤ transferGauge g K k := inv_le_transferGauge hg0 hg1 k
  have h3kn : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ k = (3 : ℝ) ^ (k - n) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have h3knpos : (0 : ℝ) < (3 : ℝ) ^ (k - n) := by positivity
  have hcut := cutoffBudget (d := d) (g := g) (K := K)
    (c := 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖)
    (T := ∫ a, S a ∂P) (k := k) (J := J) (M := M) hg1 hJ0 hmeanS hJmul
  have htailfinal := cutoffTailBound (d := d) (g := g) (K := K)
    (a := (3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P)
    (c := 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖)
    (b := (3 : ℝ) ^ ((J : ℝ) * (1 - g))) (k := k) (n := n)
    hg1 hd32 hGam1 hcut hinvGam h3kn
  -- the two comparison sizes against the printed constant
  have hGam0 : (0 : ℝ) ≤ transferGauge g K k * (3 : ℝ) ^ (k - n) := by
    nlinarith only [hGam1, h3knpos]
  have hP1 : ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
      (20 * transferGauge g K k * (3 : ℝ) ^ (k - n)) ≤
      ((6 * (d : ℝ) * Real.sqrt d * (101 / 100)) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
      (20 * transferGauge g K k * (3 : ℝ) ^ (k - n)) := by
    have h1 : (0 : ℝ) ≤ (1 / 2 * blockVecDot X (blockMatVecMul E X)) *
        (20 * transferGauge g K k * (3 : ℝ) ^ (k - n)) := by
      have : (0 : ℝ) ≤ 20 * transferGauge g K k * (3 : ℝ) ^ (k - n) := by
        linarith only [hGam0]
      exact mul_nonneg hE0 this
    have h2 : 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ ≤ 6 * (d : ℝ) * Real.sqrt d * (101 / 100) :=
      mul_le_mul_of_nonneg_left hqinv (by positivity)
    nlinarith only [h1, h2]
  have hP2 : ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * ∫ a, S a ∂P) *
          ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) *
      (1 / 2 * blockVecDot X (blockMatVecMul E X)) ≤
      (4 / 5 * ((d : ℝ) * Real.sqrt d) * transferGauge g K k * (3 : ℝ) ^ (k - n)) *
        (1 / 2 * blockVecDot X (blockMatVecMul E X)) :=
    mul_le_mul_of_nonneg_right htailfinal hE0
  -- the conclusion
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hsubq : blockVecDot X (blockMatVecMul
      (blockSub (annealedBlock P (adaptedCellTranslate q n 0))
        (annealedBlock P (centeredCube d k))) X)
      = blockVecDot X (blockMatVecMul (annealedBlock P (adaptedCellTranslate q n 0)) X) -
        blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d k)) X) := by
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, blockVecDot_blockMatVecMul_eq_dotProduct,
      blockVecDot_blockMatVecMul_eq_dotProduct, Recurrence.toFullBlockMat_blockSub,
      Matrix.sub_mulVec, dotProduct_sub]
  rw [hsubq]
  linarith only [hstep1, hhigh, hlow, hP1, hP2]

end

end Entry
end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterForward
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterReverse
public import LeanPool.HighContrastHomogenization.Provider.Selection.RoundedHops
public import LeanPool.HighContrastHomogenization.Provider.Initialization.Boundary

/-!
# High-contrast homogenization: Provider.Entry.AdapterAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted-to-Euclidean comparison constant

The comparison between adapted and Euclidean cubes, in the shape the response
and transfer proposition `p.response.transfer` binds: one constant, fixed before
the law, with the two comparison estimates at every rounded grid, every
alignment and every admissible triple of generations.

The two halves are assembled from `AdapterForward` and `AdapterReverse`.  The
cross-grid factors are the two absolute bounds of
`e.rounded.grid.bounds`: `|q^{-1}| ≤ 101/100` forward, so that
half carries no eccentricity, and `|q| ≤ (100/99)𝔢_q` in reverse, which is where
the printed `𝔢_q` enters — exactly once, as the printed statement has it.

*The constant.*  What is exhibited is `C(d,g) = 15274d^3(1-g)^{-1}`, not the
printed dimension-only `C_AE(d)`.  The reverse half reads each boundary cell of
the adapted filling through a Euclidean filling of its own, and that composition
spends one more geometric series than the printed boundary decomposition does.
The frozen consumer obligation binds its constant after the burn exponent `g`, so
the dependence is admissible there; the printed dimension-only constant would
need the boundary-shell reading of the source rather than the composed filling.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

/-- The integer power of three read as a real power of the negated difference. -/
theorem zpow_eq_rpow_neg_sub (i j : ℤ) :
    (3 : ℝ) ^ (-((j : ℝ) - (i : ℝ))) = (3 : ℝ) ^ (i - j) := by
  rw [← Real.rpow_intCast (3 : ℝ) (i - j)]
  congr 1
  push_cast
  ring

/-- **The comparison between adapted and Euclidean cubes**, in the shape the
response and transfer proposition binds: a constant fixed before the law, with
the comparison in both directions, at every rounded grid and every alignment. -/
theorem exists_euclidean_adapter (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ CAE : ℝ, 0 < CAE ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ lAl : ℤ, (kZero d : ℤ) ≤ lAl → ∀ mAl : Mat d, mAl.PosDef →
          ∀ k n m : ℤ, 0 ≤ k → k < n → n < m →
            BlockMatLoewnerLE
                (blockSub (adaptedMean P (roundedGrid lAl mAl) n)
                  (annealedBlock P (centeredCube d k)))
                (blockScale
                  (CAE * witnessEccentricity mAl * transferGauge g K k *
                    (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ)))) E) ∧
              (lAl ≤ n →
                BlockMatLoewnerLE
                  (blockSub (annealedBlock P (centeredCube d m))
                    (adaptedMean P (roundedGrid lAl mAl) n))
                  (blockScale
                    (CAE * witnessEccentricity mAl * transferGauge g K n *
                      (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) E)) := by
  classical
  have : NeZero d := ⟨by omega⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg1]
  have hinv0 : (0 : ℝ) < (1 - g)⁻¹ := inv_pos.mpr hgpos
  have hinv1 : (1 : ℝ) ≤ (1 - g)⁻¹ := by
    rw [le_inv_comm₀ one_pos hgpos]
    linarith only [hg0]
  have hd1' : 1 ≤ d := by omega
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1'
  have hsq : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt (by positivity)
  have hsqd1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hd1
  have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd1
  have hsle : Real.sqrt d ≤ (d : ℝ) := by nlinarith only [hsqd1, hsq]
  have hstep1 : (d : ℝ) * Real.sqrt d ≤ (d : ℝ) * (d : ℝ) := by
    nlinarith only [hd1, hsle]
  have hstep2 : (d : ℝ) * (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    nlinarith only [hd1, sq_nonneg ((d : ℝ))]
  have hdcube : (d : ℝ) * Real.sqrt d ≤ (d : ℝ) ^ 3 := hstep1.trans hstep2
  refine ⟨15274 * (d : ℝ) ^ 3 * (1 - g)⁻¹, by positivity, ?_⟩
  intro P E Ψ K S hP hstat _hunit hdag lAl hlAl mAl hmAl k n m hk hkn hnm
  have := hP
  have hgrid : IsRoundedGrid lAl (roundedGrid lAl mAl) := ⟨hlAl, mAl, hmAl, rfl⟩
  have hq : (roundedGrid lAl mAl).PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hqinv : ‖(roundedGrid lAl mAl)⁻¹‖ ≤ 101 / 100 :=
    Selection.norm_inv_roundedGrid_le hlAl hmAl
  have hqnorm : ‖roundedGrid lAl mAl‖ ≤ 100 / 99 * witnessEccentricity mAl :=
    Selection.norm_roundedGrid_le hlAl hmAl
  have hecc : (1 : ℝ) ≤ witnessEccentricity mAl := Initialization.one_le_witnessEccentricity hmAl
  have hn0 : (0 : ℤ) ≤ n := by omega
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hprod : (1 : ℝ) ≤ (1 - g)⁻¹ * witnessEccentricity mAl := by
    nlinarith only [hinv1, hecc]
  constructor
  · -- the forward comparison
    have hfwd := adaptedMean_sub_centeredCube_le hd1' hstat hdag hq hqinv hk hkn
    have hAM : adaptedMean P (roundedGrid lAl mAl) n =
        annealedBlock P (adaptedCell (roundedGrid lAl mAl) n) := rfl
    have hGam1 : (1 : ℝ) ≤ transferGauge g K k := by
      rw [transferGauge]
      have hbase : (1 : ℝ) ≤ 1 + K ^ 2 * (3 : ℝ) ^ (-k) := by
        have h1 : (0 : ℝ) ≤ K ^ 2 * (3 : ℝ) ^ (-k) := by positivity
        linarith only [h1]
      have hpow : (1 : ℝ) ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-k)) ^ g := Real.one_le_rpow hbase hg0
      nlinarith only [hpow, hinv1]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (k - n) := by positivity
    have hGam0 : (0 : ℝ) ≤ transferGauge g K k * (3 : ℝ) ^ (k - n) := by
      nlinarith only [hGam1, h3]
    have hcoef : 122 * (d : ℝ) * Real.sqrt d ≤
        15274 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * witnessEccentricity mAl := by
      nlinarith only [hdcube, hprod, hd3]
    have hc := mul_le_mul_of_nonneg_right hcoef hGam0
    rw [hAM, zpow_eq_rpow_neg_sub]
    intro X
    have hq2 : (0 : ℝ) ≤ blockVecDot X (blockMatVecMul E X) := by
      have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
      rw [blockVecDot_blockMatVecMul_eq_dotProduct]
      simpa using hx
    have h1 := hfwd X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h1 ⊢
    have hcq := mul_le_mul_of_nonneg_right hc
      (by linarith only [hq2] : (0 : ℝ) ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X))
    linarith only [h1, hcq]
  · -- the reverse comparison
    intro hlAln
    have hrev := centeredCube_sub_adaptedMean_le hd1' hstat hdag hgrid hqinv hlAln hn0 hnm
    have hGam1 : (1 : ℝ) ≤ transferGauge g K n := by
      rw [transferGauge]
      have hbase : (1 : ℝ) ≤ 1 + K ^ 2 * (3 : ℝ) ^ (-n) := by
        have h1 : (0 : ℝ) ≤ K ^ 2 * (3 : ℝ) ^ (-n) := by positivity
        linarith only [h1]
      have hpow : (1 : ℝ) ≤ (1 + K ^ 2 * (3 : ℝ) ^ (-n)) ^ g := Real.one_le_rpow hbase hg0
      nlinarith only [hpow, hinv1]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - m) := by positivity
    have hGam0 : (0 : ℝ) ≤ transferGauge g K n * (3 : ℝ) ^ (n - m) := by
      nlinarith only [hGam1, h3]
    have hfac0 : (0 : ℝ) ≤ 15120 * (d : ℝ) ^ 3 * (1 - g)⁻¹ := by positivity
    have hnormstep : 15120 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * ‖roundedGrid lAl mAl‖ ≤
        15120 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * (100 / 99 * witnessEccentricity mAl) :=
      mul_le_mul_of_nonneg_left hqnorm hfac0
    have hone' : (1 : ℝ) ≤ (d : ℝ) ^ 3 * ((1 - g)⁻¹ * witnessEccentricity mAl) := by
      nlinarith only [hd3, hprod]
    have hcoef : 15120 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * ‖roundedGrid lAl mAl‖ + 1 ≤
        15274 * (d : ℝ) ^ 3 * (1 - g)⁻¹ * witnessEccentricity mAl := by
      nlinarith only [hnormstep, hone']
    have hc := mul_le_mul_of_nonneg_right hcoef hGam0
    rw [zpow_eq_rpow_neg_sub]
    intro X
    have hq2 : (0 : ℝ) ≤ blockVecDot X (blockMatVecMul E X) := by
      have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
      rw [blockVecDot_blockMatVecMul_eq_dotProduct]
      simpa using hx
    have h1 := hrev X
    rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h1 ⊢
    have hcq := mul_le_mul_of_nonneg_right hc
      (by linarith only [hq2] : (0 : ℝ) ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X))
    linarith only [h1, hcq]

end

end Entry
end HighContrast
end HCPolySupport

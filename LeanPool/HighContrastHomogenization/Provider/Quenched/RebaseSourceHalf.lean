/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211Arithmetic

/-!
# High-contrast homogenization: Provider.Quenched.RebaseSourceHalf

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Source burn-in for the one-time rebase
-/

namespace HCPolySupport.HighContrast.Quenched

open HCPolySupport.IndependentSums

noncomputable section

variable {d : ℕ}

/-- The polynomial-base bracket burns the original source tail before the
inner annealed reference block is selected. -/
theorem inv_gauge_at_entry_add_bracket_le_half [NeZero d]
    {P : MeasureTheory.Measure (CoeffSpace d)} [MeasureTheory.IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K S)
    {mEnt q : ℕ}
    (hq : (2 + aspectRatio E * K) ^ 2 ≤ (3 : ℝ) ^ (q : ℤ)) :
    (Psi ((3 : ℝ) ^ ((mEnt + q : ℕ) : ℤ)))⁻¹ ≤ 1 / 2 := by
  have hA : 1 ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hK : 1 < K := hdag.one_lt_growthWitness
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hbaseK : 2 * K ≤ (2 + aspectRatio E * K) ^ 2 := by
    have hAK : K ≤ aspectRatio E * K := by
      nlinarith only [hA, hK]
    have hsum : K + 2 ≤ 2 + aspectRatio E * K := by
      linarith only [hAK]
    have hleft0 : 0 ≤ K + 2 := by linarith only [hK]
    have hright0 : 0 ≤ 2 + aspectRatio E * K := by linarith only [hsum, hleft0]
    have hsq : (K + 2) ^ 2 ≤ (2 + aspectRatio E * K) ^ 2 :=
      (sq_le_sq₀ hleft0 hright0).2 hsum
    have hleft : 2 * K ≤ (K + 2) ^ 2 := by
      nlinarith only [sq_nonneg K]
    exact hleft.trans hsq
  have hqK : 2 * K ≤ (3 : ℝ) ^ (q : ℤ) := hbaseK.trans hq
  have hmq : (3 : ℝ) ^ (q : ℤ) ≤
      (3 : ℝ) ^ ((mEnt + q : ℕ) : ℤ) := by
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have harg : 2 * K ≤ (3 : ℝ) ^ ((mEnt + q : ℕ) : ℤ) := hqK.trans hmq
  have hPsi2 : 2 ≤ Psi (2 * K) := by
    have hstep := hdag.gauge_growth (t := 2) (by norm_num)
    rw [mul_comm K 2] at hstep
    have hPsiOne : 1 ≤ Psi 2 := hdag.gauge_admissible.2 (by norm_num)
    nlinarith only [hstep, hPsiOne]
  have hmono : Psi (2 * K) ≤ Psi ((3 : ℝ) ^ ((mEnt + q : ℕ) : ℤ)) :=
    hdag.gauge_admissible.1
      (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (by positivity)) harg
  have hPsi : 2 ≤ Psi ((3 : ℝ) ^ ((mEnt + q : ℕ) : ℤ)) := hPsi2.trans hmono
  have hpos : 0 < Psi ((3 : ℝ) ^ ((mEnt + q : ℕ) : ℤ)) :=
    zero_lt_two.trans_le hPsi
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hPsi
  norm_num at hinv ⊢
  exact hinv

end

end HCPolySupport.HighContrast.Quenched

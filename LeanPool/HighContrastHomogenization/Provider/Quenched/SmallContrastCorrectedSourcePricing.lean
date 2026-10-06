/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceGroupNonneg

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedSourcePricing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrected three-channel pricing of the entry-slot source

The corrected source model (the strengthened free-threshold estimate) at the design
carriers: the entry-slot source `3·wC·(weakSourceGroupSummed …)²` splits
additively into its lag part (the two variance legs, decaying in the
window depth `n−m` with a coefficient carrying only the supply value) and
its absolute part (the bad-event leg, decaying in the generation past the
threshold), each priced by the proved leg lemmas at its **own** rate — no
common-rate coupling.  The result is exactly the three-channel model of
`hcore_body_of_corrected_family`: `bA = b0 = 1` and `b2 = 2β₂`, with the
threshold shift paid once in the third coefficient.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section


private theorem corrected_lag_source_group_bound (d : ℕ) (hd : 2 ≤ d)
    {Mabs L Csub Msc delta conv : ℝ}
     (hM0 : 0 ≤ Mabs)
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta)
    (hconv : 0 ≤ conv)
    {g : ℝ}
    {n m : ℕ}
    (hrho1 : contrastRho g < 1)
    (ha1 : (0 : ℝ) ≤ 16 * Mabs * Real.sqrt L)
    (ha2 : (0 : ℝ) ≤ Response.constantSeminormCoefficient * Mabs * Real.sqrt 7)
    : (slotVsumSharp d Csub Msc delta (n - m) ≤
      vsumSourceConstant d Csub Msc delta *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ))) ∧
    (0 ≤ slotVsumSharp d Csub Msc delta (n - m)) ∧
    (0 ≤ slotSourceSeq d Csub Msc delta (n - m) 0) ∧
    (slotSourceSeq d Csub Msc delta (n - m) 0 ≤
      slotVsumSharp d Csub Msc delta (n - m)) ∧
    (conv * slotSourceSeq d Csub Msc delta (n - m) 0 ≤
      conv * vsumSourceConstant d Csub Msc delta *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ))) ∧
    (weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 ≤
      weakSourceGroupSummed Mabs L (contrastRho g)
        (vsumSourceConstant d Csub Msc delta)
        (conv * vsumSourceConstant d Csub Msc delta) 0 *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ))) ∧
    (0 ≤ weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0) := by
  classical
  have hvleg : slotVsumSharp d Csub Msc delta (n - m) ≤
      vsumSourceConstant d Csub Msc delta *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ)) := by
    refine vsum_leg_le hd hCsub hMsc hdelta ?_
    exact le_of_eq (by ring)
  have hvs0 : 0 ≤ slotVsumSharp d Csub Msc delta (n - m) :=
    slotVsumSharp_nonneg d hCsub hMsc hdelta _
  have hseq0 : 0 ≤ slotSourceSeq d Csub Msc delta (n - m) 0 :=
    slotSourceSeq_nonneg d hCsub hMsc hdelta _ _
  have hseqle : slotSourceSeq d Csub Msc delta (n - m) 0 ≤
      slotVsumSharp d Csub Msc delta (n - m) := by
    rw [slotVsumSharp]
    have hgeom1 : (1 : ℝ) ≤ halfGeom := halfGeom_one_le
    have hpiece : (0 : ℝ) ≤ halfGeom *
        (Real.sqrt (2 * d) * 18 * Csub * Msc + Real.sqrt (2 * d) * 288 +
          deepSlotConstant d Csub Msc delta) * halfRatio ^ (n - m) := by
      have h1 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 18 * Csub * Msc := by
        positivity
      have h2 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 288 := by positivity
      have h3 : (0 : ℝ) ≤ deepSlotConstant d Csub Msc delta := by
        rw [deepSlotConstant]
        exact add_nonneg (slotSourceValue_nonneg d hCsub hMsc 0)
          (mul_nonneg (slotBaseCoefficient_nonneg d) hdelta)
      have h4 : (0 : ℝ) ≤ halfRatio ^ (n - m) :=
        pow_nonneg halfRatio_pos.le _
      have h5 : (0 : ℝ) ≤ halfGeom := by linarith only [hgeom1]
      positivity
    nlinarith only [hpiece, hgeom1, hseq0]
  have hmleg : conv * slotSourceSeq d Csub Msc delta (n - m) 0 ≤
      conv * vsumSourceConstant d Csub Msc delta *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left (hseqle.trans hvleg) hconv
    calc
      conv * slotSourceSeq d Csub Msc delta (n - m) 0 ≤
          conv * (vsumSourceConstant d Csub Msc delta *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ))) := h
      _ = conv * vsumSourceConstant d Csub Msc delta *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ)) := by ring
  -- the lag group
  have hx : weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 ≤
      weakSourceGroupSummed Mabs L (contrastRho g)
        (vsumSourceConstant d Csub Msc delta)
        (conv * vsumSourceConstant d Csub Msc delta) 0 *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ)) := by
    refine weakSourceGroupSummed_le_scaled hM0 hrho1 hvleg hmleg ?_
    rw [zero_mul]
  have hx0 : 0 ≤ weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 := by
    rw [weakSourceGroupSummed]
    have h1 := mul_nonneg ha1 hvs0
    have h2 := mul_nonneg ha2 (mul_nonneg hconv hseq0)
    have h3 : 16 * Mabs / (2 * ((1 - contrastRho g) / 2)) * 0 = 0 :=
      mul_zero _
    nlinarith only [h1, h2, h3]
  -- the bad group at its own rate
  exact ⟨hvleg, hvs0, hseq0, hseqle, hmleg, hx, hx0⟩

private theorem corrected_source_squared_decay_bounds (d : ℕ)
    {Mabs L Csub Msc delta conv K R : ℝ}
    {g : ℝ}
    {beta2 : ℝ}
    {ns n m : ℕ} (hm : ns ≤ m) (hmn : m ≤ n)
    {Delta : ℤ}
    (hy : weakSourceGroupSummed Mabs L (contrastRho g) 0 0
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)) ≤
      weakSourceGroupSummed Mabs L (contrastRho g) 0 0
        (badSourceLegConstantAtLevel L K R) *
        (3 : ℝ) ^ (-beta2 * ((n - ns : ℕ) : ℝ)))
    (hy0 : 0 ≤ weakSourceGroupSummed Mabs L (contrastRho g) 0 0
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)))
    (hx : weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 ≤
      weakSourceGroupSummed Mabs L (contrastRho g)
        (vsumSourceConstant d Csub Msc delta)
        (conv * vsumSourceConstant d Csub Msc delta) 0 *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ)))
    (hx0 : 0 ≤ weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0)
    : (weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 ^ 2 ≤
      (weakSourceGroupSummed Mabs L (contrastRho g)
    (vsumSourceConstant d Csub Msc delta)
    (conv * vsumSourceConstant d Csub Msc delta) 0) ^ 2 * (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ)))) ∧
    (weakSourceGroupSummed Mabs L (contrastRho g) 0 0
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)) ^ 2 ≤
      (weakSourceGroupSummed Mabs L (contrastRho g) 0 0
    (badSourceLegConstantAtLevel L K R)) ^ 2 * ((3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) *
        (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ))))) := by
  classical
  set X : ℝ := weakSourceGroupSummed Mabs L (contrastRho g)
    (vsumSourceConstant d Csub Msc delta)
    (conv * vsumSourceConstant d Csub Msc delta) 0 with hXdef
  set Y : ℝ := weakSourceGroupSummed Mabs L (contrastRho g) 0 0
    (badSourceLegConstantAtLevel L K R) with hYdef
  have hxsq : weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 ^ 2 ≤
      X ^ 2 * (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ))) := by
    have h := pow_le_pow_left₀ hx0 hx 2
    rw [mul_pow] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [← Real.rpow_natCast ((3 : ℝ) ^
      (-(1 / 2 : ℝ) * (((n - m : ℕ) : ℕ) : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hysq : weakSourceGroupSummed Mabs L (contrastRho g) 0 0
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)) ^ 2 ≤
      Y ^ 2 * ((3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) *
        (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ)))) := by
    have h := pow_le_pow_left₀ hy0 hy 2
    rw [mul_pow] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [← Real.rpow_natCast ((3 : ℝ) ^
      (-beta2 * ((n - ns : ℕ) : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    have hcast : ((n - ns : ℕ) : ℝ) = (n : ℝ) - (ns : ℝ) := by
      have hnsn : ns ≤ n := le_trans hm hmn
      exact Nat.cast_sub hnsn
    rw [hcast]
    ring
  -- assemble
  exact ⟨hxsq, hysq⟩
/-- **The corrected three-channel pricing of the entry-slot source.** -/
theorem corrected_source_pricing (d : ℕ) (hd : 2 ≤ d)
    {Cpre Mabs L Csub Msc delta conv K R : ℝ}
    (hCpre : 0 ≤ Cpre) (hM0 : 0 ≤ Mabs)
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta)
    (hconv : 0 ≤ conv) (hR : 1 ≤ R)
    {g : ℝ} (hg1 : g < 1)
    {beta2 : ℝ} (hb2A : beta2 ≤ contrastAlpha g)
    {ns n m : ℕ} (hm : ns ≤ m) (hmn : m ≤ n)
    {Delta : ℤ} (hD0 : 0 ≤ Delta)
    (hDrate : beta2 * ((n - ns : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * (Delta : ℝ)) :
    3 * weakCoefficient d Cpre *
      weakSourceGroupSummed Mabs L (contrastRho g)
        (slotVsumSharp d Csub Msc delta (n - m))
        (conv * slotSourceSeq d Csub Msc delta (n - m) 0)
        (Real.sqrt 2 * Real.sqrt (L + 1) *
            Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
              (R / 2) R +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
            Real.sqrt (L + 1)) ^ 2 ≤
      1 * (3 : ℝ) ^ (-(1 * (m : ℝ))) +
        (1 + 6 * weakCoefficient d Cpre *
            weakSourceGroupSummed Mabs L (contrastRho g)
              (vsumSourceConstant d Csub Msc delta)
              (conv * vsumSourceConstant d Csub Msc delta) 0 ^ 2) *
          (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ))) +
        (1 + 6 * weakCoefficient d Cpre *
            weakSourceGroupSummed Mabs L (contrastRho g) 0 0
              (badSourceLegConstantAtLevel L K R) ^ 2 *
            (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) *
          (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ))) := by
  have hrho1 : contrastRho g < 1 := contrastRho_lt_one hg1
  have hwC0 : 0 ≤ weakCoefficient d Cpre := weakCoefficient_nonneg d hCpre
  have hsL : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hsL1 : (0 : ℝ) ≤ Real.sqrt (L + 1) := Real.sqrt_nonneg _
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have ha1 : (0 : ℝ) ≤ 16 * Mabs * Real.sqrt L :=
    mul_nonneg (by linarith only [hM0]) hsL
  have ha2 : (0 : ℝ) ≤ Response.constantSeminormCoefficient * Mabs * Real.sqrt 7 :=
    mul_nonneg (mul_nonneg constantSeminormCoefficient_nonneg hM0)
      (Real.sqrt_nonneg _)
  have hden : (0 : ℝ) < 2 * ((1 - contrastRho g) / 2) := by
    linarith only [hrho1]
  have ha3 : (0 : ℝ) ≤ 16 * Mabs / (2 * ((1 - contrastRho g) / 2)) :=
    div_nonneg (by linarith only [hM0]) hden.le
  -- the lag legs at the half rate
  obtain ⟨hvleg, hvs0, hseq0, hseqle, hmleg, hx, hx0⟩ :=
    corrected_lag_source_group_bound d hd hM0 hCsub hMsc hdelta hconv
      hrho1 ha1 ha2
  have hNn0 : (0 : ℝ) ≤ ((n - ns : ℕ) : ℝ) := Nat.cast_nonneg _
  have hHrate : beta2 * ((n - ns : ℕ) : ℝ) ≤
      contrastAlpha g * ((n - ns : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hb2A hNn0
  have hbleg := bad_source_leg_at_level_le (L := L) (K := K) hR hD0 (g := g)
    (Hw := n - ns) (beta := beta2) (N := n - ns) hDrate hHrate
  have hbsrc0 : 0 ≤ Real.sqrt 2 * Real.sqrt (L + 1) *
      Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
        (R / 2) R +
      Real.sqrt 2 *
          (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
        Real.sqrt (L + 1) := by
    have hbm0 : 0 ≤ R ^ 4 * badMomentMajorant K Delta := by
      have := badMomentMajorant_nonneg K Delta
      positivity
    have hpb0 : 0 ≤ Response.profileBadMajorantAt 4
        (R ^ 4 * badMomentMajorant K Delta) (R / 2) R :=
      Response.profileBadMajorantAt_nonneg hbm0
        (by linarith only [hR] : (0 : ℝ) ≤ R / 2)
    have hp3 : (0 : ℝ) ≤ (3 : ℝ) ^
        (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have h1 := mul_nonneg (mul_nonneg hs2 hsL1) hpb0
    have h2 := mul_nonneg (mul_nonneg hs2 hp3) hsL1
    linarith only [h1, h2]
  have hy : weakSourceGroupSummed Mabs L (contrastRho g) 0 0
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)) ≤
      weakSourceGroupSummed Mabs L (contrastRho g) 0 0
        (badSourceLegConstantAtLevel L K R) *
        (3 : ℝ) ^ (-beta2 * ((n - ns : ℕ) : ℝ)) := by
    refine weakSourceGroupSummed_le_scaled hM0 hrho1 ?_ ?_ hbleg
    · rw [zero_mul]
    · rw [zero_mul]
  have hy0 : 0 ≤ weakSourceGroupSummed Mabs L (contrastRho g) 0 0
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)) := by
    rw [weakSourceGroupSummed]
    have h1 : 16 * Mabs * Real.sqrt L * 0 = 0 := mul_zero _
    have h2 : Response.constantSeminormCoefficient * Mabs * Real.sqrt 7 * 0 = 0 :=
      mul_zero _
    have h3 := mul_nonneg ha3 hbsrc0
    nlinarith only [h1, h2, h3]
  -- additivity of the group in its slots
  have hadd : weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0)
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)) =
      weakSourceGroupSummed Mabs L (contrastRho g)
        (slotVsumSharp d Csub Msc delta (n - m))
        (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 +
      weakSourceGroupSummed Mabs L (contrastRho g) 0 0
        (Real.sqrt 2 * Real.sqrt (L + 1) *
            Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
              (R / 2) R +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
            Real.sqrt (L + 1)) := by
    rw [weakSourceGroupSummed, weakSourceGroupSummed, weakSourceGroupSummed]
    ring
  -- the squared channels
  set X : ℝ := weakSourceGroupSummed Mabs L (contrastRho g)
    (vsumSourceConstant d Csub Msc delta)
    (conv * vsumSourceConstant d Csub Msc delta) 0 with hXdef
  set Y : ℝ := weakSourceGroupSummed Mabs L (contrastRho g) 0 0
    (badSourceLegConstantAtLevel L K R) with hYdef
  obtain ⟨hxsq, hysq⟩ :=
    corrected_source_squared_decay_bounds d hm hmn hy hy0 hx hx0
  have hX20 : 0 ≤ X ^ 2 := sq_nonneg X
  have hY20 : 0 ≤ Y ^ 2 := sq_nonneg Y
  have hsum2 : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
    intro x y
    nlinarith only [sq_nonneg (x - y)]
  rw [hadd]
  have hsq := hsum2 (weakSourceGroupSummed Mabs L (contrastRho g)
      (slotVsumSharp d Csub Msc delta (n - m))
      (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0)
    (weakSourceGroupSummed Mabs L (contrastRho g) 0 0
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
            (R / 2) R +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
          Real.sqrt (L + 1)))
  have hp1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 * (m : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hp2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hp3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hp4 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hchain : 3 * weakCoefficient d Cpre *
      (weakSourceGroupSummed Mabs L (contrastRho g)
          (slotVsumSharp d Csub Msc delta (n - m))
          (conv * slotSourceSeq d Csub Msc delta (n - m) 0) 0 +
        weakSourceGroupSummed Mabs L (contrastRho g) 0 0
          (Real.sqrt 2 * Real.sqrt (L + 1) *
              Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
                (R / 2) R +
            Real.sqrt 2 *
                (3 : ℝ) ^ (-((1 - contrastRho g) / 2) *
                  ((n - ns : ℕ) : ℝ)) *
              Real.sqrt (L + 1))) ^ 2 ≤
      6 * weakCoefficient d Cpre * X ^ 2 *
          (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ))) +
        6 * weakCoefficient d Cpre * Y ^ 2 *
          ((3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) *
            (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ)))) := by
    have h1 := mul_le_mul_of_nonneg_left hsq
      (by linarith only [hwC0] : (0 : ℝ) ≤ 3 * weakCoefficient d Cpre)
    have h2 := mul_le_mul_of_nonneg_left hxsq
      (by linarith only [hwC0] : (0 : ℝ) ≤ 6 * weakCoefficient d Cpre)
    have h3 := mul_le_mul_of_nonneg_left hysq
      (by linarith only [hwC0] : (0 : ℝ) ≤ 6 * weakCoefficient d Cpre)
    nlinarith only [h1, h2, h3]
  refine hchain.trans ?_
  have hc1 : 6 * weakCoefficient d Cpre * X ^ 2 *
      (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ))) ≤
      (1 + 6 * weakCoefficient d Cpre * X ^ 2) *
        (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hp2
    linarith only []
  have hc2 : 6 * weakCoefficient d Cpre * Y ^ 2 *
      ((3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) *
        (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ)))) ≤
      (1 + 6 * weakCoefficient d Cpre * Y ^ 2 *
          (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) *
        (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ))) := by
    have h : 6 * weakCoefficient d Cpre * Y ^ 2 *
        (3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) ≤
        1 + 6 * weakCoefficient d Cpre * Y ^ 2 *
          (3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) := by
      linarith only []
    calc
      6 * weakCoefficient d Cpre * Y ^ 2 *
          ((3 : ℝ) ^ (2 * beta2 * (ns : ℝ)) *
            (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ)))) =
          (6 * weakCoefficient d Cpre * Y ^ 2 *
            (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) *
            (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ))) := by ring
      _ ≤ (1 + 6 * weakCoefficient d Cpre * Y ^ 2 *
            (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) *
            (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right h hp3
  have hslack : (0 : ℝ) ≤ 1 * (3 : ℝ) ^ (-(1 * (m : ℝ))) := by
    linarith only [hp1]
  linarith only [hc1, hc2, hslack]

/-- The corrected source pricing with the entry-slot depth written in the
`min`-normalized form consumed by the corrected cadence design. -/
theorem corrected_source_pricing_min (d : ℕ) (hd : 2 ≤ d)
    {Cpre Mabs L Csub Msc delta conv K R : ℝ}
    (hCpre : 0 ≤ Cpre) (hM0 : 0 ≤ Mabs)
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta)
    (hconv : 0 ≤ conv) (hR : 1 ≤ R)
    {g : ℝ} (hg1 : g < 1)
    {beta2 : ℝ} (hb2A : beta2 ≤ contrastAlpha g)
    {ns n m : ℕ} (hm : ns ≤ m) (hmn : m ≤ n)
    {Delta : ℤ} (hD0 : 0 ≤ Delta)
    (hDrate : beta2 * ((n - ns : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * (Delta : ℝ)) :
    3 * weakCoefficient d Cpre *
      weakSourceGroupSummed Mabs L (contrastRho g)
        (slotVsumSharp d Csub Msc delta (n - min n m))
        (conv * slotSourceSeq d Csub Msc delta (n - min n m) 0)
        (Real.sqrt 2 * Real.sqrt (L + 1) *
            Response.profileBadMajorantAt 4 (R ^ 4 * badMomentMajorant K Delta)
              (R / 2) R +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((n - ns : ℕ) : ℝ)) *
            Real.sqrt (L + 1)) ^ 2 ≤
      1 * (3 : ℝ) ^ (-(1 * (m : ℝ))) +
        (1 + 6 * weakCoefficient d Cpre *
            weakSourceGroupSummed Mabs L (contrastRho g)
              (vsumSourceConstant d Csub Msc delta)
              (conv * vsumSourceConstant d Csub Msc delta) 0 ^ 2) *
          (3 : ℝ) ^ (-(1 * ((n - m : ℕ) : ℝ))) +
        (1 + 6 * weakCoefficient d Cpre *
            weakSourceGroupSummed Mabs L (contrastRho g) 0 0
              (badSourceLegConstantAtLevel L K R) ^ 2 *
            (3 : ℝ) ^ (2 * beta2 * (ns : ℝ))) *
          (3 : ℝ) ^ (-(2 * beta2 * (n : ℝ))) := by
  simpa only [min_eq_right hmn] using
    corrected_source_pricing d hd hCpre hM0 hCsub hMsc hdelta hconv hR hg1
      hb2A hm hmn hD0 hDrate

end

end HCPolySupport.HighContrast.Quenched

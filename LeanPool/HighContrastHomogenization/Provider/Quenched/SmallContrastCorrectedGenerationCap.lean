/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedConstantBounds
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitCarriers
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapReverseAdapter
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourcePolynomial

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedGenerationCap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrected generation cap

This file packages the three finite generation delays used by the endpoint.
The burn-in, deep-cap, and reverse-transfer delays are combined at the printed
base, with the coefficient and exponent table used by the corrected cadence.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix

noncomputable section

private theorem mul_le_mul_of_bounds {a b A B : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ A) (hb : b ≤ B) :
    a * b ≤ A * B :=
  mul_le_mul ha hb hb0 (le_trans ha0 ha)

/-- The burn-split depth is polynomially bounded at the endpoint base. -/
theorem three_pow_burnSplitDepth_le_corrected_base (d : ℕ) (hd : 2 ≤ d)
    {Cd g Pi base : ℝ} (hCd : 1 ≤ Cd) (hzeta : 1 ≤ zetaG g)
    (hPi : 1 ≤ Pi) (hPiBase : Pi ≤ base) :
    (3 : ℝ) ^ burnSplitDepth d Cd g Pi ≤
      (3 * ((100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d)) * base := by
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ d))
  have hx1 : (1 : ℝ) ≤
      (100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d := by
    have hCdPi : (1 : ℝ) ≤ Cd * Pi := by
      nlinarith only [hCd, hPi]
    have hCdPiZ : (1 : ℝ) ≤ Cd * Pi * zetaG g := by
      nlinarith only [hCdPi, hzeta]
    nlinarith only [hCdPiZ, hsqrt1]
  have hx0 : (0 : ℝ) <
      (100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d := by
    linarith only [hx1]
  have hceil := three_pow_ceil_logb_le
    (x := (100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d) hx0
  rw [max_eq_right hx1] at hceil
  have hdepth : (3 : ℝ) ^ burnSplitDepth d Cd g Pi ≤
      3 * ((100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d) := by
    rw [burnSplitDepth, canonicalGridEnlargement]
    exact hceil
  refine hdepth.trans ?_
  have hfac0 : (0 : ℝ) ≤
      3 * ((100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hPiBase hfac0
  calc
    3 * ((100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d) =
        (3 * ((100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d)) * Pi := by
      ring
    _ ≤ (3 * ((100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d)) * base := hmul

/-- The reverse-adapter factor is absorbed by the transfer coefficient and
the exponent `4 + 3*cW` appearing in the corrected generation table. -/
theorem max_reverseAdapterFactor_le_corrected_generation_scale
    {d : ℕ} {g K base cW Cd Cdz C5 CB CF cF : ℝ}
    {E : BlockMat d} {mAl : Mat d} {G D : ℕ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hK : 1 ≤ K)
    (hbase : 3 ≤ base) (hcW : 0 ≤ cW) (hCd : 1 ≤ Cd)
    (hzeta : 1 ≤ zetaG g)
    (hecc : witnessEccentricity mAl ≤ base)
    (hkappa1 : 1 ≤ kappaRef E) (hkappa : kappaRef E ≤ 9 / 8)
    (hgrowth : growthBar K ≤ 2 * Real.rpow base cW)
    (hGD : G + 1 = D)
    (hdepth : (3 : ℝ) ^ D ≤ C5 * base)
    (hCB : 0 ≤ CB) (hCdz : Cdz = Cd * zetaG g)
    (hCF : CF = max 1 (CB * (45 / 2) * Cdz * C5))
    (hcF : cF = 4 + 3 * cW) :
    max 1 (CB * reverseAdapterFactor Cd g K E mAl G) ≤
      CF * Real.rpow base cF := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hp1 : (1 : ℝ) ≤ Real.rpow base cW :=
    Real.one_le_rpow (by linarith only [hbase]) hcW
  have hp0 : (0 : ℝ) ≤ Real.rpow base cW := by
    linarith only [hp1]
  have hgrowth2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hgrowth0 : (0 : ℝ) ≤ growthBar K := by
    linarith only [hgrowth2]
  have hKbar : K ≤ growthBar K := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ K := by linarith only [hK]
  have hKsq : K ^ (2 : ℕ) ≤ growthBar K ^ (2 : ℕ) :=
    pow_le_pow_left₀ hK0 hKbar 2
  have hgaugePre : (1 + K ^ (2 : ℕ)) ^ g ≤
      2 + K ^ (2 : ℕ) := by
    have h := rpow_le_one_add (y := 1 + K ^ (2 : ℕ)) (c := g)
      (by positivity) hg.1 (by linarith only [hg.2])
    nlinarith only [h]
  have hgaugeGrowth : (1 + K ^ (2 : ℕ)) ^ g ≤
      2 * growthBar K ^ (2 : ℕ) := by
    have hsq4 : (4 : ℝ) ≤ growthBar K ^ (2 : ℕ) := by
      nlinarith only [hgrowth2]
    nlinarith only [hgaugePre, hKsq, hsq4]
  have hgrowthSq : growthBar K ^ (2 : ℕ) ≤
      4 * Real.rpow base cW ^ (2 : ℕ) := by
    have hs := pow_le_pow_left₀ hgrowth0 hgrowth 2
    nlinarith only [hs]
  have hgauge : (1 + K ^ (2 : ℕ)) ^ g ≤
      8 * Real.rpow base cW ^ (2 : ℕ) := by
    nlinarith only [hgaugeGrowth, hgrowthSq]
  have hgauge0 : (0 : ℝ) ≤ (1 + K ^ (2 : ℕ)) ^ g := by
    positivity
  have hT1 : IndependentSums.natTriangular 1 + 1 = 1 := by decide
  have hmom0 : (0 : ℝ) ≤ sourceMomentOne K := by
    linarith only [one_le_sourceMomentOne (K := K)]
  have hmomGrowth : sourceMomentOne K ≤ 3 * growthBar K := by
    have h := sourceMomentOne_le K
    rwa [hT1, pow_one] at h
  have hmom : sourceMomentOne K ≤ 6 * Real.rpow base cW := by
    nlinarith only [hmomGrowth, hgrowth]
  have hecc0 : (0 : ℝ) ≤ witnessEccentricity mAl := Real.sqrt_nonneg _
  have hkappa0 : (0 : ℝ) ≤ kappaRef E := by
    linarith only [hkappa1]
  have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd]
  have hzeta0 : (0 : ℝ) ≤ zetaG g := by linarith only [hzeta]
  have hCdz0 : (0 : ℝ) ≤ Cdz := by
    rw [hCdz]
    exact mul_nonneg hCd0 hzeta0
  have hboundary : boundaryConst Cd g mAl ≤ Cdz * base := by
    rw [boundaryConst, hCdz]
    have hfac0 : (0 : ℝ) ≤ Cd * zetaG g := mul_nonneg hCd0 hzeta0
    calc
      Cd * witnessEccentricity mAl * zetaG g =
          (Cd * zetaG g) * witnessEccentricity mAl := by ring
      _ ≤ (Cd * zetaG g) * base :=
        mul_le_mul_of_nonneg_left hecc hfac0
      _ = Cd * zetaG g * base := by ring
  have hboundary0 : (0 : ℝ) ≤ boundaryConst Cd g mAl := by
    rw [boundaryConst]
    positivity
  have hGR : (g * (G : ℝ)) ≤ (D : ℝ) := by
    have hGle : G ≤ D := by omega
    have hG0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg _
    have hgG : g * (G : ℝ) ≤ (G : ℝ) := by
      nlinarith only [hg.1, hg.2, hG0]
    have hcast : (G : ℝ) ≤ (D : ℝ) := by exact_mod_cast hGle
    linarith only [hgG, hcast]
  have htail : Real.rpow (3 : ℝ) (g * (G : ℝ)) ≤ C5 * base := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hGR
    calc
      Real.rpow (3 : ℝ) (g * (G : ℝ)) ≤
          Real.rpow (3 : ℝ) (D : ℝ) := hmono
      _ = (3 : ℝ) ^ D := Real.rpow_natCast 3 D
      _ ≤ C5 * base := hdepth
  have htail0 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (g * (G : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hC50 : (0 : ℝ) ≤ C5 := by
    have hpowD : (0 : ℝ) < (3 : ℝ) ^ D := by positivity
    have hprodPos : (0 : ℝ) < C5 * base := lt_of_lt_of_le hpowD hdepth
    rcases mul_pos_iff.mp hprodPos with hpos | hneg
    · exact hpos.1.le
    · exact False.elim (not_lt_of_ge hbase0.le hneg.2)
  have hgrid0 : (0 : ℝ) ≤ gridReferenceRatio Cd g K E mAl G := by
    rw [gridReferenceRatio]
    positivity
  have hinner1 := mul_le_mul_of_bounds hmom0 hboundary0 hmom hboundary
  have hinner1R0 : (0 : ℝ) ≤
      (6 * Real.rpow base cW) * (Cdz * base) := by positivity
  have hinner2 := mul_le_mul_of_bounds
    (mul_nonneg hmom0 hboundary0) htail0 hinner1 htail
  have hinner2R0 : (0 : ℝ) ≤
      ((6 * Real.rpow base cW) * (Cdz * base)) * (C5 * base) := by
    positivity
  have hinner3 := mul_le_mul_of_bounds hkappa0
    (mul_nonneg (mul_nonneg hmom0 hboundary0) htail0) hkappa hinner2
  have hinner3R0 : (0 : ℝ) ≤
      (9 / 8 : ℝ) *
        (((6 * Real.rpow base cW) * (Cdz * base)) * (C5 * base)) := by
    positivity
  have hinner4 := mul_le_mul_of_bounds hgauge0
    (mul_nonneg hkappa0 (mul_nonneg (mul_nonneg hmom0 hboundary0) htail0))
    hgauge hinner3
  have hinner4R0 : (0 : ℝ) ≤
      (8 * Real.rpow base cW ^ (2 : ℕ)) *
        ((9 / 8 : ℝ) *
          (((6 * Real.rpow base cW) * (Cdz * base)) * (C5 * base))) := by
    positivity
  have hinner4' : (1 + K ^ (2 : ℕ)) ^ g *
      gridReferenceRatio Cd g K E mAl G ≤
      (8 * Real.rpow base cW ^ (2 : ℕ)) *
        ((9 / 8 : ℝ) *
          (((6 * Real.rpow base cW) * (Cdz * base)) * (C5 * base))) := by
    rw [gridReferenceRatio]
    exact hinner4
  have hfactor := mul_le_mul_of_bounds hecc0
    (mul_nonneg hgauge0 hgrid0) hecc hinner4'
  have hfactor' : reverseAdapterFactor Cd g K E mAl G ≤
      54 * Cdz * C5 * base ^ (3 : ℕ) *
        Real.rpow base cW ^ (3 : ℕ) := by
    rw [reverseAdapterFactor]
    calc
      reverseAdapterFactor Cd g K E mAl G ≤
          base * ((8 * Real.rpow base cW ^ (2 : ℕ)) *
            ((9 / 8 : ℝ) *
              (((6 * Real.rpow base cW) * (Cdz * base)) *
                (C5 * base)))) := hfactor
      _ = 54 * Cdz * C5 * base ^ (3 : ℕ) *
          Real.rpow base cW ^ (3 : ℕ) := by ring
  have hfactor0 : (0 : ℝ) ≤ reverseAdapterFactor Cd g K E mAl G := by
    rw [reverseAdapterFactor]
    exact mul_nonneg hecc0 (mul_nonneg hgauge0 hgrid0)
  have hCBfactor : CB * reverseAdapterFactor Cd g K E mAl G ≤
      CB * (45 / 2) * Cdz * C5 *
        (base ^ (4 : ℕ) * Real.rpow base cW ^ (3 : ℕ)) := by
    have hstep := mul_le_mul_of_nonneg_left hfactor' hCB
    have hcoef : (54 : ℝ) ≤ (45 / 2) * base := by
      nlinarith only [hbase]
    have hrest0 : (0 : ℝ) ≤
        CB * Cdz * C5 * base ^ (3 : ℕ) *
          Real.rpow base cW ^ (3 : ℕ) := by positivity
    have hcoefStep := mul_le_mul_of_nonneg_right hcoef hrest0
    calc
      CB * reverseAdapterFactor Cd g K E mAl G ≤
          CB * (54 * Cdz * C5 * base ^ (3 : ℕ) *
            Real.rpow base cW ^ (3 : ℕ)) := hstep
      _ = 54 * (CB * Cdz * C5 * base ^ (3 : ℕ) *
          Real.rpow base cW ^ (3 : ℕ)) := by ring
      _ ≤ (45 / 2 * base) *
          (CB * Cdz * C5 * base ^ (3 : ℕ) *
            Real.rpow base cW ^ (3 : ℕ)) := hcoefStep
      _ = CB * (45 / 2) * Cdz * C5 *
          (base ^ (4 : ℕ) * Real.rpow base cW ^ (3 : ℕ)) := by ring
  have hmerge : Real.rpow base cF =
      base ^ (4 : ℕ) * Real.rpow base cW ^ (3 : ℕ) := by
    rw [hcF]
    have h4 : Real.rpow base (4 : ℝ) = base ^ (4 : ℕ) :=
      Real.rpow_natCast base 4
    have hthree : Real.rpow base (3 * cW) =
        Real.rpow base cW ^ (3 : ℕ) := by
      calc
        Real.rpow base (3 * cW) =
            Real.rpow base ((cW + cW) + cW) := by congr 1; ring
        _ = Real.rpow base (cW + cW) * Real.rpow base cW :=
          Real.rpow_add hbase0 (cW + cW) cW
        _ = (Real.rpow base cW * Real.rpow base cW) *
            Real.rpow base cW := by
          exact congrArg (fun x => x * Real.rpow base cW)
            (Real.rpow_add hbase0 cW cW)
        _ = Real.rpow base cW ^ (3 : ℕ) := by ring
    calc
      Real.rpow base (4 + 3 * cW) =
          Real.rpow base 4 * Real.rpow base (3 * cW) :=
        Real.rpow_add hbase0 4 (3 * cW)
      _ = base ^ (4 : ℕ) * Real.rpow base cW ^ (3 : ℕ) := by
        exact congrArg₂ (· * ·) h4 hthree
  have hCF1 : (1 : ℝ) ≤ CF := by
    rw [hCF]
    exact le_max_left _ _
  have hcF0 : (0 : ℝ) ≤ cF := by
    rw [hcF]
    linarith only [hcW]
  have hright1 : (1 : ℝ) ≤ CF * Real.rpow base cF := by
    have hp : (1 : ℝ) ≤ Real.rpow base cF :=
      Real.one_le_rpow (by linarith only [hbase]) hcF0
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ CF * Real.rpow base cF :=
        mul_le_mul hCF1 hp zero_le_one (by linarith only [hCF1])
  refine max_le hright1 ?_
  rw [hCF, hmerge]
  exact hCBfactor.trans (mul_le_mul_of_nonneg_right
    (le_max_right (1 : ℝ) (CB * (45 / 2) * Cdz * C5)) (by positivity))

/-- The maximum of the three finite delay components obeys the generation
coefficient and exponent table used by the initial cadence level schedule. -/
theorem corrected_generation_power_cap
    (d : ℕ) (hd : 2 ≤ d)
    {H D G ns nB nE nF : ℕ}
    {g K Pi base cW rate Cd Cdz C5 CE CB CF cF Cns cns : ℝ}
    {E : BlockMat d} {mAl : Mat d}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hK : 1 ≤ K)
    (hPi : 1 ≤ Pi) (hPiBase : Pi ≤ base)
    (hbase : 3 ≤ base) (hcW : 0 ≤ cW) (hrate : 0 < rate)
    (hCd : 1 ≤ Cd) (hzeta : 1 ≤ zetaG g)
    (hecc : witnessEccentricity mAl ≤ base)
    (hkappa1 : 1 ≤ kappaRef E) (hkappa : kappaRef E ≤ 9 / 8)
    (hgrowth : growthBar K ≤ 2 * Real.rpow base cW)
    (hD : D = burnSplitDepth d Cd g Pi) (hGD : G + 1 = D)
    (hCB : 0 ≤ CB) (hCdz : Cdz = Cd * zetaG g)
    (hC5 : C5 = 3 * ((100 / 99 : ℝ) * Cd * zetaG g * Real.sqrt d))
    (hCE : CE = 8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ))
    (hCF : CF = max 1 (CB * (45 / 2) * Cdz * C5))
    (hcF : cF = 4 + 3 * cW)
    (hCns : Cns = (3 : ℝ) ^ (H + 1) * 624 * CE *
      (3 * Real.rpow CF rate⁻¹) * 3)
    (hcns : cns = 4 * cW + 4 + cF / rate)
    (hnsSum : ns ≤ (H + 1) + nB + nE + nF)
    (hB : (3 : ℝ) ^ nB ≤ 3 * (13 * growthBar K ^ (4 : ℕ)))
    (hE : (3 : ℝ) ^ nE ≤
      8100 * (3 : ℝ) ^ (3 * H) * (3 : ℝ) ^ (4 * D))
    (hF : (3 : ℝ) ^ nF ≤
      3 * Real.rpow
        (max 1 (CB * reverseAdapterFactor Cd g K E mAl G)) rate⁻¹) :
    (3 : ℝ) ^ ns ≤ Cns * Real.rpow base cns := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hp0 : (0 : ℝ) ≤ Real.rpow base cW :=
    Real.rpow_nonneg hbase0.le cW
  have hp1 : (1 : ℝ) ≤ Real.rpow base cW :=
    Real.one_le_rpow (by linarith only [hbase]) hcW
  have hgrowth0 : (0 : ℝ) ≤ growthBar K := by
    linarith only [show (2 : ℝ) ≤ growthBar K from le_max_left _ _]
  have hp4 : Real.rpow base cW ^ (4 : ℕ) =
      Real.rpow base (4 * cW) := by
    calc
      Real.rpow base cW ^ (4 : ℕ) =
          Real.rpow (Real.rpow base cW) (4 : ℝ) :=
        (Real.rpow_natCast (Real.rpow base cW) 4).symm
      _ = Real.rpow base (cW * 4) := by
        change (base ^ cW) ^ (4 : ℝ) = base ^ (cW * 4)
        rw [← Real.rpow_mul hbase0.le]
      _ = Real.rpow base (4 * cW) := by ring_nf
  have hBnorm : (3 : ℝ) ^ nB ≤
      624 * Real.rpow base (4 * cW) := by
    have hpow := pow_le_pow_left₀ hgrowth0 hgrowth 4
    have hcalc : 3 * (13 * growthBar K ^ (4 : ℕ)) ≤
        624 * Real.rpow base (4 * cW) := by
      rw [← hp4]
      nlinarith only [hpow]
    exact hB.trans hcalc
  have hdepth : (3 : ℝ) ^ D ≤ C5 * base := by
    rw [hD, hC5]
    exact three_pow_burnSplitDepth_le_corrected_base d hd hCd hzeta hPi hPiBase
  have hdepth0 : (0 : ℝ) ≤ (3 : ℝ) ^ D := by positivity
  have hdepthPow := pow_le_pow_left₀ hdepth0 hdepth 4
  have hDpow : ((3 : ℝ) ^ D) ^ (4 : ℕ) =
      (3 : ℝ) ^ (4 * D) := by
    rw [← pow_mul]
    congr 1
    ring
  have hEnorm : (3 : ℝ) ^ nE ≤ CE * Real.rpow base 4 := by
    have hstep : (3 : ℝ) ^ (4 * D) ≤
        (C5 * base) ^ (4 : ℕ) := by
      rw [← hDpow]
      exact hdepthPow
    calc
      (3 : ℝ) ^ nE ≤
          8100 * (3 : ℝ) ^ (3 * H) * (3 : ℝ) ^ (4 * D) := hE
      _ ≤ 8100 * (3 : ℝ) ^ (3 * H) * (C5 * base) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (8100 * (3 : ℝ) ^ (3 * H) * C5 ^ (4 : ℕ)) *
          base ^ (4 : ℕ) := by ring
      _ = CE * base ^ (4 : ℕ) := by rw [hCE]
      _ = CE * Real.rpow base 4 := by
        exact congrArg (fun x : ℝ => CE * x)
          (Real.rpow_natCast base 4).symm
  have hrv := max_reverseAdapterFactor_le_corrected_generation_scale
    hg hK hbase hcW hCd hzeta hecc hkappa1 hkappa hgrowth hGD hdepth hCB
    hCdz hCF hcF
  have hrv0 : (0 : ℝ) ≤
      max 1 (CB * reverseAdapterFactor Cd g K E mAl G) :=
    le_trans zero_le_one (le_max_left _ _)
  have hinv0 : (0 : ℝ) ≤ rate⁻¹ := inv_nonneg.mpr hrate.le
  have hrvPow := Real.rpow_le_rpow hrv0 hrv hinv0
  have hCF0 : (0 : ℝ) ≤ CF := by
    rw [hCF]
    exact le_trans zero_le_one (le_max_left _ _)
  have hbasecF0 : (0 : ℝ) ≤ Real.rpow base cF :=
    Real.rpow_nonneg hbase0.le cF
  have hsplit : Real.rpow (CF * Real.rpow base cF) rate⁻¹ =
      Real.rpow CF rate⁻¹ * Real.rpow base (cF / rate) := by
    calc
      Real.rpow (CF * Real.rpow base cF) rate⁻¹ =
          Real.rpow CF rate⁻¹ *
            Real.rpow (Real.rpow base cF) rate⁻¹ :=
        Real.mul_rpow hCF0 hbasecF0
      _ = Real.rpow CF rate⁻¹ * Real.rpow base (cF / rate) := by
        congr 1
        change (base ^ cF) ^ rate⁻¹ = base ^ (cF / rate)
        rw [← Real.rpow_mul hbase0.le]
        rw [div_eq_mul_inv]
  have hFnorm : (3 : ℝ) ^ nF ≤
      (3 * Real.rpow CF rate⁻¹) * Real.rpow base (cF / rate) := by
    calc
      (3 : ℝ) ^ nF ≤
          3 * Real.rpow
            (max 1 (CB * reverseAdapterFactor Cd g K E mAl G)) rate⁻¹ := hF
      _ ≤ 3 * Real.rpow (CF * Real.rpow base cF) rate⁻¹ :=
        mul_le_mul_of_nonneg_left hrvPow (by norm_num)
      _ = (3 * Real.rpow CF rate⁻¹) * Real.rpow base (cF / rate) := by
        rw [hsplit]
        ring
  have hnsMono : (3 : ℝ) ^ ns ≤
      (3 : ℝ) ^ ((H + 1) + nB + nE + nF) :=
    pow_le_pow_right₀ (by norm_num) hnsSum
  have hsplitNat : (3 : ℝ) ^ ((H + 1) + nB + nE + nF) =
      (3 : ℝ) ^ (H + 1) * (3 : ℝ) ^ nB *
        (3 : ℝ) ^ nE * (3 : ℝ) ^ nF := by
    rw [pow_add, pow_add, pow_add]
  have hH0 : (0 : ℝ) ≤ (3 : ℝ) ^ (H + 1) := by positivity
  have hB0 : (0 : ℝ) ≤ (3 : ℝ) ^ nB := by positivity
  have hE0 : (0 : ℝ) ≤ (3 : ℝ) ^ nE := by positivity
  have hF0 : (0 : ℝ) ≤ (3 : ℝ) ^ nF := by positivity
  have hprodB := mul_le_mul_of_nonneg_left hBnorm hH0
  have hprodE := mul_le_mul_of_bounds
    (mul_nonneg hH0 hB0) hE0 hprodB hEnorm
  have hprodF := mul_le_mul_of_bounds
    (mul_nonneg (mul_nonneg hH0 hB0) hE0) hF0 hprodE hFnorm
  have hbaseMerge :
      Real.rpow base (4 * cW) * Real.rpow base 4 *
          Real.rpow base (cF / rate) = Real.rpow base cns := by
    rw [hcns]
    calc
      Real.rpow base (4 * cW) * Real.rpow base 4 *
          Real.rpow base (cF / rate) =
          Real.rpow base (4 * cW + 4) *
          Real.rpow base (cF / rate) := by
        congr 1
        exact (Real.rpow_add hbase0 (4 * cW) 4).symm
      _ = Real.rpow base (4 * cW + 4 + cF / rate) := by
        exact (Real.rpow_add hbase0 (4 * cW + 4) (cF / rate)).symm
  have hcoeff0 : (0 : ℝ) ≤
      (3 : ℝ) ^ (H + 1) * 624 * CE *
        (3 * Real.rpow CF rate⁻¹) := by
    have hCE0 : (0 : ℝ) ≤ CE := by
      rw [hCE]
      positivity
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by norm_num)) hCE0)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hCF0 rate⁻¹))
  calc
      (3 : ℝ) ^ ns ≤ (3 : ℝ) ^ ((H + 1) + nB + nE + nF) := hnsMono
    _ = (3 : ℝ) ^ (H + 1) * (3 : ℝ) ^ nB *
        (3 : ℝ) ^ nE * (3 : ℝ) ^ nF := hsplitNat
    _ ≤ ((3 : ℝ) ^ (H + 1) *
          (624 * Real.rpow base (4 * cW)) *
          (CE * Real.rpow base 4)) *
        ((3 * Real.rpow CF rate⁻¹) * Real.rpow base (cF / rate)) := hprodF
    _ = ((3 : ℝ) ^ (H + 1) * 624 * CE *
          (3 * Real.rpow CF rate⁻¹)) * Real.rpow base cns := by
      rw [← hbaseMerge]
      ring
    _ ≤ (((3 : ℝ) ^ (H + 1) * 624 * CE *
          (3 * Real.rpow CF rate⁻¹)) * 3) * Real.rpow base cns := by
      have hscale : (3 : ℝ) ^ (H + 1) * 624 * CE *
          (3 * Real.rpow CF rate⁻¹) ≤
          ((3 : ℝ) ^ (H + 1) * 624 * CE *
            (3 * Real.rpow CF rate⁻¹)) * 3 := by
        nlinarith only [hcoeff0]
      exact mul_le_mul_of_nonneg_right hscale
        (Real.rpow_nonneg hbase0.le cns)
    _ = Cns * Real.rpow base cns := by rw [hCns]

end

end HCPolySupport.HighContrast.Quenched

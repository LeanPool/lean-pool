/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueBasePar

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakValueIsoAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp weak value at a released split level

The parallel copy of `weakValueBoundSharpIsotropyAt` with the three coefficients the
released weak-norm chain produces — the recent group's, the maximum group's and
the window tail's — and the bad-event majorant at a free threshold pair.  At
`(16, 16, √2)` and `(1 / 2, 1)` it is the pinned value on the nose.

The second declaration is the metric-factor comparison at the released
carriers.  It absorbs the released window-tail coefficient into the maximum
group's, which is what lets the parametrized base keep its pinned tail: a
`ctail` above `√2` is paid for by multiplying the maximum group's coefficient
by it, and the bad slot only gains.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **The sharp weak value at a released split level.**  Three free
coefficients and a free threshold pair. -/
@[expose]
def weakValueBoundSharpIsotropyAt (cfirst cmax ctail : ℝ)
    (P : Measure (CoeffSpace d)) (m0 h0 : Mat d)
    (F : BlockMat d) (L : ℝ) (n : Mat d) (rho : ℝ) (Hw : ℕ)
    (bmaj beta lev : ℝ) (t l : ℤ)
    (V : ℕ → ℝ) (V0 : ℝ) (Dr : ℕ → ℝ) (Vmean : ℝ) : ℝ :=
  (cfirst * Response.diagonalWeakMetricFactor m0 (Response.skewBlockCongr h0 F) *
      Real.sqrt L *
      ((∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
        ∑ j ∈ Finset.range (Hw + 1),
          (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
            Real.sqrt (2 * d * Dr j)) +
    cmax * Response.diagonalWeakMetricFactor m0 (Response.skewBlockCongr h0 F) /
        (2 * ((1 - rho) / 2)) *
      (Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 bmaj beta lev +
        ctail * (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) *
          Real.sqrt (L + 1)) +
    Response.constantSeminormCoefficient *
      (Response.diagonalWeakMetricFactor m0
          (Response.skewBlockCongr h0 (adaptedMean P (roundedGrid l n) t)) *
        Real.sqrt 7 * Vmean)) ^ 2

/-- **The sharp weak value is monotone in the metric factors, at a released
split level.**  The window tail's coefficient is absorbed into the maximum
group's, so the parametrized base is read at its pinned tail. -/
theorem weakValueBoundSharpIsotropyAt_le_baseIsotropyAtPar_sq [NeZero d]
    {P : Measure (CoeffSpace d)} {m0 h0 : Mat d} {n : Mat d}
    {Eref : BlockMat d}
    {cfirst cmax ctail L M rho bmaj beta lev : ℝ} {Hw : ℕ} {t l : ℤ}
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax)
    (hctail : Real.sqrt 2 ≤ ctail)
    (hrho1 : rho < 1) (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0)
    (hDr : ∀ j, 0 ≤ Dr j) (hVmean : 0 ≤ Vmean)
    (hbmaj : 0 ≤ bmaj) (hbeta : 0 ≤ beta)
    (hMF2 : Response.diagonalWeakMetricFactor m0 (Response.skewBlockCongr h0 Eref) ≤ M)
    (hMFmean : Response.diagonalWeakMetricFactor m0
        (Response.skewBlockCongr h0 (adaptedMean P (roundedGrid l n) t)) ≤ M) :
    weakValueBoundSharpIsotropyAt cfirst cmax ctail P m0 h0 Eref L n rho Hw
        bmaj beta lev t l V V0 Dr Vmean ≤
      weakValueBaseIsotropyAtPar (d := d) cfirst (cmax * ctail) M L rho Hw
        bmaj beta lev V V0 Dr Vmean ^ 2 := by
  classical
  set MF2 : ℝ := Response.diagonalWeakMetricFactor m0
    (Response.skewBlockCongr h0 Eref) with hMF2def
  set MFm : ℝ := Response.diagonalWeakMetricFactor m0
    (Response.skewBlockCongr h0 (adaptedMean P (roundedGrid l n) t)) with hMFmdef
  have hMF20 : 0 ≤ MF2 := Response.diagonalWeakMetricFactor_nonneg _ _
  have hMFm0 : 0 ≤ MFm := Response.diagonalWeakMetricFactor_nonneg _ _
  have hM0 : 0 ≤ M := le_trans hMF20 hMF2
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hctail0 : 0 ≤ ctail := le_trans hs2.le hctail
  set S1 : ℝ := ∑ j ∈ Finset.range (Hw + 1),
    (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j) with hS1
  set S2 : ℝ := ∑ j ∈ Finset.range (Hw + 1),
    (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
      Real.sqrt (2 * d * Dr j) with hS2
  have hS10 : 0 ≤ S1 := by
    rw [hS1]
    refine Finset.sum_nonneg fun j _ => ?_
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hv : 0 ≤ V j + V0 + Dr j := by linarith only [hV j, hV0, hDr j]
    exact mul_nonneg h3 hv
  have hS20 : 0 ≤ S2 := by
    rw [hS2]
    refine Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hcoef : (0 : ℝ) < 2 * ((1 - rho) / 2) := by linarith only [hrho1]
  have hcSem : (0 : ℝ) ≤ Response.constantSeminormCoefficient := by
    rw [Response.constantSeminormCoefficient_eq]
    have hlt : (3 : ℝ) ^ (-(1 : ℝ) / 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 : ℝ) / 2) := by
      linarith only [hlt]
    positivity
  set PB : ℝ := Response.profileBadMajorantAt 4 bmaj beta lev with hPB
  have hPB0 : 0 ≤ PB := Response.profileBadMajorantAt_nonneg hbmaj hbeta
  set T : ℝ := (3 : ℝ) ^ (-((1 - rho) / 2) * (Hw : ℝ)) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hL10 : (0 : ℝ) ≤ Real.sqrt (L + 1) := Real.sqrt_nonneg _
  -- the first group
  have hg1 : cfirst * MF2 * Real.sqrt L * (S1 + S2) ≤
      cfirst * M * Real.sqrt L * (S1 + S2) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith only [hS10, hS20])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMF2 hcfirst) (Real.sqrt_nonneg _)
  -- the maximum group, with the tail coefficient absorbed
  have hbadterm : cmax * MF2 / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB) ≤
      cmax * ctail * M / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB) := by
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (mul_nonneg hs2.le hL10) hPB0)
    refine div_le_div_of_nonneg_right ?_ hcoef.le
    have hstep : cmax * MF2 ≤ cmax * M :=
      mul_le_mul_of_nonneg_left hMF2 hcmax
    have hone : (1 : ℝ) ≤ ctail := by
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith only [h1, hctail]
    have hcM : 0 ≤ cmax * M := mul_nonneg hcmax hM0
    calc
      cmax * MF2 ≤ cmax * M := hstep
      _ = (cmax * M) * 1 := by ring
      _ ≤ (cmax * M) * ctail := mul_le_mul_of_nonneg_left hone hcM
      _ = cmax * ctail * M := by ring
  have htailterm : cmax * MF2 / (2 * ((1 - rho) / 2)) *
        (ctail * T * Real.sqrt (L + 1)) ≤
      cmax * ctail * M / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * T * Real.sqrt (L + 1)) := by
    have hrw1 : cmax * MF2 / (2 * ((1 - rho) / 2)) *
        (ctail * T * Real.sqrt (L + 1)) =
        cmax * ctail * MF2 / (2 * ((1 - rho) / 2)) *
          (T * Real.sqrt (L + 1)) := by
      field_simp
    have hrw2 : cmax * ctail * M / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * T * Real.sqrt (L + 1)) =
        cmax * ctail * (Real.sqrt 2 * M) / (2 * ((1 - rho) / 2)) *
          (T * Real.sqrt (L + 1)) := by
      field_simp
    rw [hrw1, hrw2]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hT0 hL10)
    refine div_le_div_of_nonneg_right ?_ hcoef.le
    have hMle : MF2 ≤ Real.sqrt 2 * M := by
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      calc
        MF2 ≤ M := hMF2
        _ = 1 * M := by ring
        _ ≤ Real.sqrt 2 * M := mul_le_mul_of_nonneg_right h1 hM0
    exact mul_le_mul_of_nonneg_left hMle (mul_nonneg hcmax hctail0)
  have hg2 : cmax * MF2 / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB + ctail * T * Real.sqrt (L + 1)) ≤
      cmax * ctail * M / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB +
          Real.sqrt 2 * T * Real.sqrt (L + 1)) := by
    have hL : cmax * MF2 / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB +
          ctail * T * Real.sqrt (L + 1)) =
        cmax * MF2 / (2 * ((1 - rho) / 2)) *
            (Real.sqrt 2 * Real.sqrt (L + 1) * PB) +
          cmax * MF2 / (2 * ((1 - rho) / 2)) *
            (ctail * T * Real.sqrt (L + 1)) := by ring
    have hR : cmax * ctail * M / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB +
          Real.sqrt 2 * T * Real.sqrt (L + 1)) =
        cmax * ctail * M / (2 * ((1 - rho) / 2)) *
            (Real.sqrt 2 * Real.sqrt (L + 1) * PB) +
          cmax * ctail * M / (2 * ((1 - rho) / 2)) *
            (Real.sqrt 2 * T * Real.sqrt (L + 1)) := by ring
    rw [hL, hR]
    exact add_le_add hbadterm htailterm
  -- the seminorm group
  have hg3 : Response.constantSeminormCoefficient * (MFm * Real.sqrt 7 * Vmean) ≤
      Response.constantSeminormCoefficient * (M * Real.sqrt 7 * Vmean) := by
    refine mul_le_mul_of_nonneg_left ?_ hcSem
    refine mul_le_mul_of_nonneg_right ?_ hVmean
    exact mul_le_mul_of_nonneg_right hMFmean (Real.sqrt_nonneg _)
  have hbase0 : 0 ≤ cfirst * MF2 * Real.sqrt L * (S1 + S2) +
      cmax * MF2 / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB +
          ctail * T * Real.sqrt (L + 1)) +
      Response.constantSeminormCoefficient * (MFm * Real.sqrt 7 * Vmean) := by
    have h1 : 0 ≤ cfirst * MF2 * Real.sqrt L * (S1 + S2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hcfirst hMF20) (Real.sqrt_nonneg _))
        (by linarith only [hS10, hS20])
    have hin : 0 ≤ Real.sqrt 2 * Real.sqrt (L + 1) * PB +
        ctail * T * Real.sqrt (L + 1) := by
      have ha : 0 ≤ Real.sqrt 2 * Real.sqrt (L + 1) * PB :=
        mul_nonneg (mul_nonneg hs2.le hL10) hPB0
      have hb : 0 ≤ ctail * T * Real.sqrt (L + 1) :=
        mul_nonneg (mul_nonneg hctail0 hT0) hL10
      linarith only [ha, hb]
    have h2 : 0 ≤ cmax * MF2 / (2 * ((1 - rho) / 2)) *
        (Real.sqrt 2 * Real.sqrt (L + 1) * PB +
          ctail * T * Real.sqrt (L + 1)) :=
      mul_nonneg (div_nonneg (mul_nonneg hcmax hMF20) hcoef.le) hin
    have h3 : 0 ≤ Response.constantSeminormCoefficient *
        (MFm * Real.sqrt 7 * Vmean) :=
      mul_nonneg hcSem
        (mul_nonneg (mul_nonneg hMFm0 (Real.sqrt_nonneg _)) hVmean)
    linarith only [h1, h2, h3]
  rw [weakValueBoundSharpIsotropyAt, weakValueBaseIsotropyAtPar, ← hS1, ← hS2, ← hPB,
    ← hT]
  exact pow_le_pow_left₀ hbase0 (by linarith only [hg1, hg2, hg3]) 2

end

end HCPolySupport.HighContrast.Quenched

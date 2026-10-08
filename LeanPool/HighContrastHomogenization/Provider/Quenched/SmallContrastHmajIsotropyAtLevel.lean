/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueIsoAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHmajIsotropyAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `hmaj` slot at a released split level

The value-side clause of the line producer, at the released weak value.  The
chain is the pinned one with three constants and one threshold pair carried as
parameters: the metric-factor comparison, the isotropy carriers' instantiation,
the generation-indexed family, and the law-free weakening of the normalizer.

The normalizer's linearity is what makes the last step work at any
coefficients: every group of the parametrized base carries the normalizer as a
factor, so the base is `M` times its value at `M = 1`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The normalizer is a factor -/

/-- **The parametrized base is linear in the normalizer.** -/
theorem weakValueBaseIsotropyAtPar_eq_mul (cfirst cmax M L rho : ℝ) (Hw : ℕ)
    (bmaj beta lev : ℝ) (V : ℕ → ℝ) (V0 : ℝ) (Dr : ℕ → ℝ) (Vmean : ℝ) :
    weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L rho Hw bmaj beta lev
        V V0 Dr Vmean =
      M * weakValueBaseIsotropyAtPar (d := d) cfirst cmax 1 L rho Hw bmaj beta lev
        V V0 Dr Vmean := by
  rw [weakValueBaseIsotropyAtPar, weakValueBaseIsotropyAtPar]
  ring

/-- **The parametrized base is monotone in the normalizer.** -/
theorem weakValueBaseIsotropyAtPar_mono_M {cfirst cmax M M' L rho : ℝ} {Hw : ℕ}
    {bmaj beta lev : ℝ} {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax) (hMM : M ≤ M') (hrho1 : rho < 1)
    (hbmaj : 0 ≤ bmaj) (hbeta : 0 ≤ beta)
    (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0) (hDr : ∀ j, 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean) :
    weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L rho Hw bmaj beta lev
        V V0 Dr Vmean ≤
      weakValueBaseIsotropyAtPar (d := d) cfirst cmax M' L rho Hw bmaj beta lev
        V V0 Dr Vmean := by
  have hZ0 : 0 ≤ weakValueBaseIsotropyAtPar (d := d) cfirst cmax 1 L rho Hw
      bmaj beta lev V V0 Dr Vmean :=
    weakValueBaseIsotropyAtPar_nonneg hcfirst hcmax zero_le_one hrho1 hbmaj hbeta
      hV hV0 hDr hVmean
  rw [weakValueBaseIsotropyAtPar_eq_mul cfirst cmax M,
    weakValueBaseIsotropyAtPar_eq_mul cfirst cmax M']
  exact mul_le_mul_of_nonneg_right hMM hZ0

/-! ## The `hmaj` position at a released split level -/

/-- **The `hmaj` position at an abstract envelope scalar, released.** -/
theorem weak_value_le_baseIsotropyAtPar_sq_at_scalar_at_level
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    {c kapc L rho bmaj beta lev cfirst cmax ctail : ℝ} {Hw : ℕ} {t l : ℤ}
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hrec : canonicalShear E = 0)
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat
        (adaptedMean P (roundedGrid l (canonicalMetric E)) t) =
      schurBlock S0 SStar0 K0)
    (hc : 0 ≤ c) (hkapc : 0 ≤ kapc)
    (henv : BlockMatLoewnerLE
      (adaptedMean P (roundedGrid l (canonicalMetric E)) t)
      (blockScale c E))
    (hcomp : BlockMatLoewnerLE E
      (blockScale kapc
        (adaptedMean P (roundedGrid l (canonicalMetric E)) t)))
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax)
    (hctail : Real.sqrt 2 ≤ ctail)
    (hrho1 : rho < 1)
    (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0) (hDr : ∀ j, 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean) (hbad : 0 ≤ bmaj) (hbeta : 0 ≤ beta) :
    weakValueBoundSharpIsotropyAt cfirst cmax ctail P (canonicalMetric E)
        (Response.responseSkew K0) (blockScale c E) L (canonicalMetric E) rho Hw
        bmaj beta lev t l V V0 Dr Vmean ≤
      weakValueBaseIsotropyAtPar (d := d) cfirst (cmax * ctail)
        (metricFactorValue E c kapc) L rho Hw bmaj beta lev
        V V0 Dr Vmean ^ 2 := by
  obtain ⟨hMF2, hMFmean⟩ := diagonalWeakMetricFactor_recentered_le hE hEpd
    hsharp hrec hS0 hStar0 hform hc hkapc henv hcomp
  exact weakValueBoundSharpIsotropyAt_le_baseIsotropyAtPar_sq hcfirst hcmax hctail
    hrho1 hV hV0 hDr hVmean hbad hbeta hMF2 hMFmean

/-- **The `hmaj` position at the isotropy carriers, released.** -/
theorem weak_value_le_baseIsotropyAtPar_sq_at_isotropy_at_level
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    {cIso kap rho bmaj beta lev cfirst cmax ctail : ℝ} {Hw : ℕ} {t l : ℤ}
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hrec : canonicalShear E = 0)
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat
        (adaptedMean P (roundedGrid l (canonicalMetric E)) t) =
      schurBlock S0 SStar0 K0)
    (hcIso : 0 ≤ cIso) (hsmall : cIso < 1)
    (henv : BlockMatLoewnerLE
      (adaptedMean P (roundedGrid l (canonicalMetric E)) t)
      (isotropyReference cIso E))
    (hcomp : BlockMatLoewnerLE E
      (blockScale (isotropyKap2 cIso)
        (adaptedMean P (roundedGrid l (canonicalMetric E)) t)))
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax)
    (hctail : Real.sqrt 2 ≤ ctail)
    (hrho1 : rho < 1)
    (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0) (hDr : ∀ j, 0 ≤ Dr j)
    (hVmean : 0 ≤ Vmean) (hbad : 0 ≤ bmaj) (hbeta : 0 ≤ beta) :
    weakValueBoundSharpIsotropyAt cfirst cmax ctail P (canonicalMetric E)
        (Response.responseSkew K0) (isotropyReference cIso E)
        (isotropyLoadScale cIso kap) (canonicalMetric E) rho Hw
        bmaj beta lev t l V V0 Dr Vmean ≤
      weakValueBaseIsotropyAtPar (d := d) cfirst (cmax * ctail)
        (metricFactorValue E (1 + cIso) (isotropyKap2 cIso))
        (isotropyLoadScale cIso kap) rho Hw bmaj beta lev
        V V0 Dr Vmean ^ 2 := by
  have hkapc : 0 ≤ isotropyKap2 cIso := by
    rw [isotropyKap2]
    exact inv_nonneg.mpr (by linarith only [hsmall])
  exact weak_value_le_baseIsotropyAtPar_sq_at_scalar_at_level
    (L := isotropyLoadScale cIso kap)
    hE hEpd hsharp hrec hS0 hStar0 hform (by linarith only [hcIso]) hkapc
    henv hcomp hcfirst hcmax hctail hrho1 hV hV0 hDr hVmean hbad hbeta

/-- **`hmaj` at the isotropy carriers, released.** -/
theorem hmaj_at_isotropy_at_level
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hrec : canonicalShear E = 0)
    {cIso rho : ℝ} (hcIso : 0 ≤ cIso) (hcsmall : cIso < 1) (hrho1 : rho < 1)
    {Hw : ℕ} {lAl : ℤ} {N₀ : ℕ}
    {S0 SStar0 K0 : ℕ → Mat d}
    (hS0 : ∀ n : ℕ, (S0 n).PosDef) (hStar0 : ∀ n : ℕ, (SStar0 n).PosDef)
    (hform : ∀ n : ℕ,
      toFullBlockMat (adaptedMean P (roundedGrid lAl (canonicalMetric E))
          ((N₀ : ℤ) + (n : ℤ))) =
        schurBlock (S0 n) (SStar0 n) (K0 n))
    (henv : ∀ n : ℕ,
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid lAl (canonicalMetric E))
          ((N₀ : ℤ) + (n : ℤ)))
        (isotropyReference cIso E))
    (hcomp : ∀ n : ℕ,
      BlockMatLoewnerLE E
        (blockScale (isotropyKap2 cIso)
          (adaptedMean P (roundedGrid lAl (canonicalMetric E))
            ((N₀ : ℤ) + (n : ℤ)))))
    {V : ℕ → ℕ → ℝ} {V0 : ℕ → ℝ} {Dr : ℕ → ℕ → ℝ} {Vmean : ℕ → ℝ}
    {bmaj : ℕ → ℝ} {beta lev cfirst cmax ctail : ℝ}
    (hV : ∀ n j : ℕ, 0 ≤ V n j) (hV0 : ∀ n : ℕ, 0 ≤ V0 n)
    (hDr : ∀ n j : ℕ, 0 ≤ Dr n j) (hVmean : ∀ n : ℕ, 0 ≤ Vmean n)
    (hbmaj : ∀ n : ℕ, 0 ≤ bmaj n) (hbeta : 0 ≤ beta)
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax)
    (hctail : Real.sqrt 2 ≤ ctail) :
    ∀ n : ℕ,
      weakValueBoundSharpIsotropyAt cfirst cmax ctail P (canonicalMetric E)
          (Response.responseSkew (K0 n)) (isotropyReference cIso E)
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (canonicalMetric E)
          rho Hw (bmaj n) beta lev ((N₀ : ℤ) + (n : ℤ)) lAl
          (V n) (V0 n) (Dr n) (Vmean n) ≤
        weakValueBaseIsotropyAtPar (d := d) cfirst (cmax * ctail)
            (metricFactorValue E (1 + cIso) (isotropyKap2 cIso))
            (isotropyLoadScale cIso (isotropyKap2 cIso)) rho Hw (bmaj n)
            beta lev (V n) (V0 n) (Dr n) (Vmean n) ^ 2 :=
  fun n =>
    weak_value_le_baseIsotropyAtPar_sq_at_isotropy_at_level hE hEpd hsharp hrec
      (hS0 n) (hStar0 n) (hform n) hcIso hcsmall (henv n) (hcomp n) hcfirst
      hcmax hctail hrho1 (hV n) (hV0 n) (hDr n) (hVmean n) (hbmaj n) hbeta

/-- **`hmaj` at a law-free normalizer, released.**  The normalizer is weakened
to any upper bound, which is what the endpoint's binder requires of it. -/
theorem hmaj_at_isotropy_of_metric_bound_at_level
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hrec : canonicalShear E = 0)
    {cIso rho : ℝ} (hcIso : 0 ≤ cIso) (hcsmall : cIso < 1) (hrho1 : rho < 1)
    {Hw : ℕ} {lAl : ℤ} {N₀ : ℕ}
    {S0 SStar0 K0 : ℕ → Mat d}
    (hS0 : ∀ n : ℕ, (S0 n).PosDef) (hStar0 : ∀ n : ℕ, (SStar0 n).PosDef)
    (hform : ∀ n : ℕ,
      toFullBlockMat (adaptedMean P (roundedGrid lAl (canonicalMetric E))
          ((N₀ : ℤ) + (n : ℤ))) =
        schurBlock (S0 n) (SStar0 n) (K0 n))
    (henv : ∀ n : ℕ,
      BlockMatLoewnerLE
        (adaptedMean P (roundedGrid lAl (canonicalMetric E))
          ((N₀ : ℤ) + (n : ℤ)))
        (isotropyReference cIso E))
    (hcomp : ∀ n : ℕ,
      BlockMatLoewnerLE E
        (blockScale (isotropyKap2 cIso)
          (adaptedMean P (roundedGrid lAl (canonicalMetric E))
            ((N₀ : ℤ) + (n : ℤ)))))
    {V : ℕ → ℕ → ℝ} {V0 : ℕ → ℝ} {Dr : ℕ → ℕ → ℝ} {Vmean : ℕ → ℝ}
    {bmaj : ℕ → ℝ} {beta lev cfirst cmax ctail : ℝ}
    (hV : ∀ n j : ℕ, 0 ≤ V n j) (hV0 : ∀ n : ℕ, 0 ≤ V0 n)
    (hDr : ∀ n j : ℕ, 0 ≤ Dr n j) (hVmean : ∀ n : ℕ, 0 ≤ Vmean n)
    (hbmaj : ∀ n : ℕ, 0 ≤ bmaj n) (hbeta : 0 ≤ beta)
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax)
    (hctail : Real.sqrt 2 ≤ ctail)
    {M' : ℝ}
    (hM' : metricFactorValue E (1 + cIso) (isotropyKap2 cIso) ≤ M') :
    ∀ n : ℕ,
      weakValueBoundSharpIsotropyAt cfirst cmax ctail P (canonicalMetric E)
          (Response.responseSkew (K0 n)) (isotropyReference cIso E)
          (isotropyLoadScale cIso (isotropyKap2 cIso)) (canonicalMetric E)
          rho Hw (bmaj n) beta lev ((N₀ : ℤ) + (n : ℤ)) lAl
          (V n) (V0 n) (Dr n) (Vmean n) ≤
        weakValueBaseIsotropyAtPar (d := d) cfirst (cmax * ctail) M'
            (isotropyLoadScale cIso (isotropyKap2 cIso)) rho Hw (bmaj n)
            beta lev (V n) (V0 n) (Dr n) (Vmean n) ^ 2 := by
  intro n
  have hcmt : 0 ≤ cmax * ctail :=
    mul_nonneg hcmax (le_trans (Real.sqrt_nonneg 2) hctail)
  refine le_trans
    (hmaj_at_isotropy_at_level hE hEpd hsharp hrec hcIso hcsmall hrho1 hS0
      hStar0 hform henv hcomp hV hV0 hDr hVmean hbmaj hbeta hcfirst hcmax
      hctail n) ?_
  have hbase0 : 0 ≤ weakValueBaseIsotropyAtPar (d := d) cfirst (cmax * ctail)
      (metricFactorValue E (1 + cIso) (isotropyKap2 cIso))
      (isotropyLoadScale cIso (isotropyKap2 cIso)) rho Hw (bmaj n) beta lev
      (V n) (V0 n) (Dr n) (Vmean n) :=
    weakValueBaseIsotropyAtPar_nonneg hcfirst hcmt (metricFactorValue_nonneg _ _ _)
      hrho1 (hbmaj n) hbeta (hV n) (hV0 n) (hDr n) (hVmean n)
  exact pow_le_pow_left₀ hbase0
    (weakValueBaseIsotropyAtPar_mono_M hcfirst hcmt hM' hrho1 (hbmaj n) hbeta
      (hV n) (hV0 n) (hDr n) (hVmean n)) 2

end

end HCPolySupport.HighContrast.Quenched

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHmajIsotropyAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastValueClauseAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastValueClauseAtCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The value clause at the design carriers

The released one-step family reports its weak value at the isotropy reference,
the scalar load and the generation's own window; the fused core asks for that
value below the parametrized base at the pinned group coefficients.  This file
joins the two at the exact spelling the family produces, so the assembly has
nothing left to reconcile on the value side.

The window is read at the generation's own height by instantiating the
fixed-window statement once per generation — the value clause is universally
quantified over the height, so no restatement is needed for a growing window.

The released window-tail coefficient is above the pinned one because the split
level is at least one, which is the printed range's left endpoint.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The pinned window tail is below the released one on the printed range. -/
theorem sqrt_two_le_energyGoodConstantAtLevel {lev : ℝ} (hlev : 1 ≤ lev) :
    Real.sqrt 2 ≤ Response.energyGoodConstantAtLevel lev := by
  rw [Response.energyGoodConstantAtLevel]
  exact Real.sqrt_le_sqrt (by linarith only [hlev])

/-- The normalizer the value clause hands the fused core. -/
@[expose]
def designNormalizer (lev M : ℝ) : ℝ :=
  absorbedNormalizer (Response.recentConstantAtLevel lev)
    (Response.maxGroupConstantAtLevel lev * Response.energyGoodConstantAtLevel lev) M

theorem designNormalizer_nonneg {lev M : ℝ} (hlev : 1 ≤ lev) (hM : 0 ≤ M) :
    0 ≤ designNormalizer lev M := by
  have hct : (0 : ℝ) ≤ Response.energyGoodConstantAtLevel lev :=
    le_trans (Real.sqrt_nonneg 2) (sqrt_two_le_energyGoodConstantAtLevel hlev)
  exact absorbedNormalizer_nonneg (Response.zero_le_recentConstantAtLevel lev)
    (mul_nonneg (Response.zero_le_maxGroupConstantAtLevel lev) hct) hM

/-- **The value clause at the design carriers, at the pinned coefficients.**
This is the fused core's value hypothesis, produced from the released chain at
the spelling the released one-step family reports. -/
theorem hmaj_at_design_carriers_at_level [NeZero d]
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    (hrec : canonicalShear E = 0)
    {cIso rho : ℝ} (hcIso : 0 ≤ cIso) (hcsmall : cIso < 1) (hrho1 : rho < 1)
    {lAl : ℤ} {N₀ : ℕ}
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
    {bmaj : ℕ → ℝ} {beta lev : ℝ} {Hw : ℕ → ℕ}
    (hV : ∀ n j : ℕ, 0 ≤ V n j) (hV0 : ∀ n : ℕ, 0 ≤ V0 n)
    (hDr : ∀ n j : ℕ, 0 ≤ Dr n j) (hVmean : ∀ n : ℕ, 0 ≤ Vmean n)
    (hbmaj : ∀ n : ℕ, 0 ≤ bmaj n) (hbeta : 0 ≤ beta) (hlev : 1 ≤ lev)
    {M : ℝ} (hM : metricFactorValue E (1 + cIso) (isotropyKap2 cIso) ≤ M) :
    ∀ n : ℕ,
      weakValueBoundSharpIsotropyAt (Response.recentConstantAtLevel lev)
          (Response.maxGroupConstantAtLevel lev)
          (Response.energyGoodConstantAtLevel lev)
          P (canonicalMetric E) (Response.responseSkew (K0 n))
          (isotropyReference cIso E)
          (loadScaleOfScalar (1 + cIso) (isotropyKap2 cIso))
          (canonicalMetric E) rho (Hw n) (bmaj n) beta lev
          ((N₀ : ℤ) + (n : ℤ)) lAl (V n) (V0 n) (Dr n) (Vmean n) ≤
        weakValueBaseIsotropyAtPar (d := d) 16 16 (designNormalizer lev M)
          (isotropyLoadScale cIso (isotropyKap2 cIso)) rho (Hw n) (bmaj n)
          beta lev (V n) (V0 n) (Dr n) (Vmean n) ^ 2 := by
  intro n
  have hct : Real.sqrt 2 ≤ Response.energyGoodConstantAtLevel lev :=
    sqrt_two_le_energyGoodConstantAtLevel hlev
  have hM0 : (0 : ℝ) ≤ M :=
    le_trans (metricFactorValue_nonneg _ _ _) hM
  have hraw := hmaj_at_isotropy_of_metric_bound_at_level (Hw := Hw n)
    (beta := beta) (lev := lev) (cfirst := Response.recentConstantAtLevel lev)
    (cmax := Response.maxGroupConstantAtLevel lev)
    (ctail := Response.energyGoodConstantAtLevel lev)
    hE hEpd hsharp hrec hcIso hcsmall hrho1 hS0 hStar0 hform henv hcomp
    hV hV0 hDr hVmean hbmaj hbeta
    (Response.zero_le_recentConstantAtLevel lev)
    (Response.zero_le_maxGroupConstantAtLevel lev) hct hM n
  exact le_baseIsotropyAtPar_pinned_of_atLevel
    (Response.zero_le_recentConstantAtLevel lev)
    (mul_nonneg (Response.zero_le_maxGroupConstantAtLevel lev)
      (le_trans (Real.sqrt_nonneg 2) hct)) hM0 hrho1 (hbmaj n) hbeta
    (hV n) (hV0 n) (hDr n) (hVmean n) hraw

end

end HCPolySupport.HighContrast.Quenched

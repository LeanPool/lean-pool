/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastValueClauseAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpLineAtJb
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSplitSupplyAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValueBasePar

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastFamilyLineClausesSrc

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The family recursion with the explicit source

The line chain of `SmallContrastSharpLineAtJb` through
`SmallContrastFamilyLineClausesSrc`, with the entry pricing clause removed:
the per-generation recursion carries the entry-slot source term
`3·wC·(weakSourceGroupSummed …)²` **explicitly**, so the corrected
three-channel pricing can be applied to it downstream instead of the
geometric pre-pricing of the availability route.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- `hrec_final_sharp_at_jb_src` with the source kept explicit. -/
theorem hrec_final_sharp_at_jb_src {F : ℕ → ℝ}
    (hFnn : ∀ j, 0 ≤ F j) (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {n H jb : ℕ} (hH : H + 1 ≤ n) (hjbn : jb ≤ n)
    {a bq cw : ℝ} (ha : 0 ≤ a) (hbq0 : 0 ≤ bq) (hcw : 0 ≤ cw)
    {W u v w cdrop : ℝ} (hW0 : 0 ≤ W)
    (hstep : F n ≤ a * (F (n - H) - F n) + bq * F n ^ 2 + cw * W ^ 2)
    (hWsplit : W ≤ u + v * F jb + w)
    (hwsq : w ^ 2 ≤ cdrop * iterationDropSum r F n)
    {A : ℝ}
    (hA1 : a * (r ^ H)⁻¹ + 3 * cw * cdrop ≤ A)
    (hA2 : bq + 3 * cw * v ^ 2 ≤ A) :
    F n ≤ A * iterationDropSum r F n + A * F jb ^ 2 + 3 * cw * u ^ 2 := by
  have hbase := hrec_of_one_step_sharp_at_jb hFnn hFmono hr0 hr1 hH hjbn ha
    hbq0 hcw hW0 hstep hWsplit hwsq
  have hT0 : 0 ≤ iterationDropSum r F n :=
    iterationDropSum_nonneg hFmono hr0.le n
  have h1 : (a * (r ^ H)⁻¹ + 3 * cw * cdrop) * iterationDropSum r F n ≤
      A * iterationDropSum r F n :=
    mul_le_mul_of_nonneg_right hA1 hT0
  have h2 : (bq + 3 * cw * v ^ 2) * F jb ^ 2 ≤ A * F jb ^ 2 :=
    mul_le_mul_of_nonneg_right hA2 (sq_nonneg _)
  linarith only [hbase, h1, h2]

/-- `per_generation_hrec_at_recursionAlpha_sharp_at_jb_src` with the source
kept explicit. -/
theorem per_generation_hrec_at_recursionAlpha_sharp_at_jb_src {F : ℕ → ℝ}
    {g : ℝ} (hg1 : g < 1)
    (hFnn : ∀ j, 0 ≤ F j) (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    {n H jb : ℕ} (hH : H + 1 ≤ n) (hjbn : jb ≤ n)
    {a bq cw : ℝ} (ha : 0 ≤ a) (hbq0 : 0 ≤ bq) (hcw : 0 ≤ cw)
    {W u v w cdrop : ℝ} (hW0 : 0 ≤ W)
    (hstep : F n ≤ a * (F (n - H) - F n) + bq * F n ^ 2 + cw * W ^ 2)
    (hWsplit : W ≤ u + v * F jb + w)
    (hwsq : w ^ 2 ≤ cdrop *
      iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g)) F n)
    {A : ℝ}
    (hA1 : a * ((((3 : ℝ) ^ (-recursionAlpha g)) ^ H)⁻¹) +
      3 * cw * cdrop ≤ A)
    (hA2 : bq + 3 * cw * v ^ 2 ≤ A) :
    F n ≤ A * iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g)) F n +
      A * F jb ^ 2 + 3 * cw * u ^ 2 := by
  obtain ⟨hr0, hr1⟩ := ratio_mem_Ioo hg1
  exact hrec_final_sharp_at_jb_src hFnn hFmono hr0 hr1 hH hjbn ha hbq0 hcw
    hW0 hstep hWsplit hwsq hA1 hA2

/-- `hrec_line_of_one_step_isotropy_sharp_at_jb_src` with the source kept
explicit. -/
theorem hrec_line_of_one_step_isotropy_sharp_at_jb_src
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {N₀ n H jb : ℕ} (hH : H + 1 ≤ n) (hjbn : jb ≤ n)
    (hFnn : ∀ j, 0 ≤ hatExcess P q N₀ j)
    (hFmono : ∀ p j : ℕ, p ≤ j → hatExcess P q N₀ j ≤ hatExcess P q N₀ p)
    {g : ℝ} (hg1 : g < 1)
    {Cpre eta : ℝ} {cRow kap : ℝ}
    (hCpre : 0 ≤ Cpre) (heta : 0 < eta)
    {wv W u v w cdrop A : ℝ} (hW0 : 0 ≤ W) (hmaj : wv ≤ W ^ 2)
    (hquad0 : 0 ≤ quadCoefficient d Cpre (rowCoefficientIsotropy d cRow kap))
    (hone : adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
            (16 * (d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
          rowValue2Isotropy d cRow kap
            ((d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) + wv) +
        2 * ((3 * (d : ℝ) + 4) *
          ((d : ℝ) *
            (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) ^ 2))
    (hWsplit : W ≤ u + v * hatExcess P q N₀ jb + w)
    (hwsq : w ^ 2 ≤ cdrop *
      iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g)) (hatExcess P q N₀) n)
    (hA1 : dropCoefficient d Cpre eta *
        ((((3 : ℝ) ^ (-recursionAlpha g)) ^ H)⁻¹) +
        3 * weakCoefficient d Cpre * cdrop ≤ A)
    (hA2 : quadCoefficient d Cpre (rowCoefficientIsotropy d cRow kap) +
        3 * weakCoefficient d Cpre * v ^ 2 ≤ A) :
    hatExcess P q N₀ n ≤
      A * iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g))
          (hatExcess P q N₀) n +
        A * hatExcess P q N₀ jb ^ 2 +
        3 * weakCoefficient d Cpre * u ^ 2 := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hstep := one_step_to_scalar_step_isotropy d hd0 hCpre hmaj hone
  have hT : (d : ℝ) * (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1) =
      hatExcess P q N₀ n := rfl
  have hS : (d : ℝ) *
      (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) - 1) =
      hatExcess P q N₀ (n - H) := rfl
  rw [hT, hS] at hstep
  exact per_generation_hrec_at_recursionAlpha_sharp_at_jb_src hg1 hFnn hFmono
    hH hjbn (dropCoefficient_nonneg d hCpre heta) hquad0
    (weakCoefficient_nonneg d hCpre) hW0 hstep hWsplit hwsq hA1 hA2

/-- The released sharp slot line, with the source kept explicit. -/
theorem hrec_line_of_slots_isotropy_sharp_at_jb_at_level_src
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {N₀ n H Hw jb : ℕ}
    (hH : H + 1 ≤ n) (hHw : Hw + 1 ≤ n) (hjbn : jb ≤ n)
    (hFnn : ∀ j, 0 ≤ hatExcess P q N₀ j)
    (hFmono : ∀ p j : ℕ, p ≤ j → hatExcess P q N₀ j ≤ hatExcess P q N₀ p)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1)
    {Cpre eta : ℝ} {cRow kap : ℝ}
    (hCpre : 0 ≤ Cpre) (heta : 0 < eta)
    (hcRow : 0 ≤ cRow) (hkap : 0 ≤ kap)
    {M L : ℝ} (hM0 : 0 ≤ M)
    {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    {bmaj beta lev : ℝ}
    (hV : ∀ j, 0 ≤ V j) (hV0 : 0 ≤ V0) (hDrnn : ∀ j, 0 ≤ Dr j)
    (hVmean0 : 0 ≤ Vmean) (hbmaj : 0 ≤ bmaj) (hbeta : 0 ≤ beta)
    {wv : ℝ}
    (hmaj : wv ≤
      weakValueBaseIsotropyAtPar (d := d) 16 16 M L (contrastRho g) Hw
        bmaj beta lev V V0 Dr Vmean ^ 2)
    (hone : adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
            (16 * (d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
          rowValue2Isotropy d cRow kap
            ((d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) + wv) +
        2 * ((3 * (d : ℝ) + 4) *
          ((d : ℝ) *
            (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) ^ 2))
    {vsum cVsum vmsrc cVm bsrc cD delta : ℝ}
    (hcD0 : 0 ≤ cD) (hdelta0 : 0 ≤ delta)
    (hVsum : (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0)) ≤
      vsum + cVsum * hatExcess P q N₀ jb)
    (hVmeanle : Vmean ≤ vmsrc + cVm * hatExcess P q N₀ jb)
    (hDrdelta : ∀ j ∈ Finset.range (Hw + 1), Dr j ≤ delta)
    (hDrdrop : ∀ j ∈ Finset.range (Hw + 1),
      Dr j ≤ cD * (hatExcess P q N₀ (n - j) - hatExcess P q N₀ n))
    (hbad : Real.sqrt 2 * Real.sqrt (L + 1) *
            Response.profileBadMajorantAt 4 bmaj beta lev +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) *
            Real.sqrt (L + 1) ≤ bsrc)
    :
    hatExcess P q N₀ n ≤
      fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
          cVsum cVm *
          iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g))
            (hatExcess P q N₀) n +
        fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
            cVsum cVm * hatExcess P q N₀ jb ^ 2 +
          3 * weakCoefficient d Cpre *
            weakSourceGroupSummed M L (contrastRho g) vsum vmsrc bsrc ^ 2 := by
  obtain ⟨w, hw0, hbase, hwsq⟩ :=
    split_at_recursionAlpha_at_level (d := d) (M := M) (L := L) (Hw := Hw) (V := V)
      (V0 := V0) (Dr := Dr) (Vmean := Vmean) (F := hatExcess P q N₀) (n := n)
      (jb := jb) (vsum := vsum) (cVsum := cVsum) (vmsrc := vmsrc) (cVm := cVm)
      (bsrc := bsrc) (cD := cD) (delta := delta) (g := g) (bmaj := bmaj)
      (beta := beta) (lev := lev)
      hFmono hM0 hg0 hg1 hHw hcD0 hdelta0 hVsum hVmeanle hDrnn hDrdelta
      hDrdrop hbad
  have hW0 : 0 ≤ weakValueBaseIsotropyAtPar (d := d) 16 16 M L (contrastRho g) Hw
        bmaj beta lev
      V V0 Dr Vmean :=
    weakValueBaseIsotropyAtPar_nonneg (by norm_num) (by norm_num) hM0
      (contrastRho_lt_one hg1) hbmaj hbeta hV hV0 hDrnn hVmean0
  have hWsplit : weakValueBaseIsotropyAtPar (d := d) 16 16 M L (contrastRho g) Hw
        bmaj beta lev
      V V0 Dr Vmean ≤
      weakSourceGroupSummed M L (contrastRho g) vsum vmsrc bsrc +
        weakBaseCoefficientSummed M L cVsum cVm * hatExcess P q N₀ jb + w := by
    rw [weakValueBaseIsotropyAtPar]
    exact hbase
  have hquad0 : 0 ≤ quadCoefficient d Cpre (rowCoefficientIsotropy d cRow kap) :=
    quadCoefficient_nonneg d hCpre (rowCoefficientIsotropy_nonneg hcRow hkap)
  exact hrec_line_of_one_step_isotropy_sharp_at_jb_src hH hjbn hFnn hFmono hg1
    hCpre heta hW0 hmaj hquad0 hone hWsplit hwsq
    (hA1_of_fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap
      cD delta cVsum cVm)
    (hA2_of_fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap
      cD delta cVsum cVm)

/-- The line producer with the source kept explicit. -/
theorem hline_of_slots_sharp_var_at_jb_at_level_src
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {N₀ ns H : ℕ} {Hw : ℕ → ℕ}
    {g Cpre eta cRow kap M L cD delta : ℝ}
    (hconst : IsotropySlotConstants d g Cpre eta cRow kap M cD delta)
    (hFnn : ∀ j, 0 ≤ hatExcess P q N₀ j)
    (hFmono : ∀ p j : ℕ, p ≤ j → hatExcess P q N₀ j ≤ hatExcess P q N₀ p)
    {V : ℕ → ℕ → ℝ} {V0 : ℕ → ℝ} {Dr : ℕ → ℕ → ℝ} {Vmean : ℕ → ℝ}
    {bmaj : ℕ → ℝ} {beta lev : ℝ} {wv : ℕ → ℝ} {jb : ℕ → ℕ}
    {cVsum cVm : ℝ} {vsum vmsrc bsrc : ℕ → ℝ}
    (hV : ∀ n j, 0 ≤ V n j) (hV0 : ∀ n, 0 ≤ V0 n)
    (hDrnn : ∀ n j, 0 ≤ Dr n j) (hVmean0 : ∀ n, 0 ≤ Vmean n)
    (hbmaj : ∀ n, 0 ≤ bmaj n) (hbeta : 0 ≤ beta)
    (hbad : ∀ n : ℕ, Real.sqrt 2 * Real.sqrt (L + 1) *
            Response.profileBadMajorantAt 4 (bmaj n) beta lev +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((Hw n : ℕ) : ℝ)) *
            Real.sqrt (L + 1) ≤ bsrc n)
    (hH : ∀ n : ℕ, ns ≤ n → H + 1 ≤ n)
    (hHw : ∀ n : ℕ, ns ≤ n → Hw n + 1 ≤ n)
    (hjbn : ∀ n : ℕ, ns ≤ n → jb n ≤ n)
    (hmaj : ∀ n : ℕ, ns ≤ n → wv n ≤
      weakValueBaseIsotropyAtPar (d := d) 16 16 M L (contrastRho g) (Hw n)
        (bmaj n) beta lev (V n)
        (V0 n) (Dr n) (Vmean n) ^ 2)
    (hone : ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
            (16 * (d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
          rowValue2Isotropy d cRow kap
            ((d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) + wv n) +
        2 * ((3 * (d : ℝ) + 4) *
          ((d : ℝ) *
            (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) ^ 2))
    (hVsum : ∀ n : ℕ, ns ≤ n → (∑ j ∈ Finset.range (Hw n + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V n j + V0 n)) ≤
      vsum n + cVsum * hatExcess P q N₀ (jb n))
    (hVmeanle : ∀ n : ℕ, ns ≤ n →
      Vmean n ≤ vmsrc n + cVm * hatExcess P q N₀ (jb n))
    (hDrdelta : ∀ n : ℕ, ns ≤ n → ∀ j ∈ Finset.range (Hw n + 1),
      Dr n j ≤ delta)
    (hDrdrop : ∀ n : ℕ, ns ≤ n → ∀ j ∈ Finset.range (Hw n + 1),
      Dr n j ≤ cD * (hatExcess P q N₀ (n - j) - hatExcess P q N₀ n))
    :
    ∀ n : ℕ, ns ≤ n →
      hatExcess P q N₀ n ≤
        fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
            cVsum cVm *
            iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g))
              (hatExcess P q N₀) n +
          fusionRecursionConstantIsotropySharp d Cpre eta H M L g cRow kap cD delta
              cVsum cVm * hatExcess P q N₀ (jb n) ^ 2 +
            3 * weakCoefficient d Cpre *
              weakSourceGroupSummed M L (contrastRho g) (vsum n) (vmsrc n)
                (bsrc n) ^ 2 := by
  intro n hn
  exact hrec_line_of_slots_isotropy_sharp_at_jb_at_level_src (hH n hn) (hHw n hn)
    (hjbn n hn) hFnn hFmono hconst.hg0 hconst.hg1 hconst.hCpre hconst.heta
    hconst.hcRow hconst.hkap hconst.hM0 (hV n) (hV0 n) (hDrnn n) (hVmean0 n)
    (hbmaj n) hbeta (hmaj n hn) (hone n hn) hconst.hcD0 hconst.hdelta0
    (hVsum n hn) (hVmeanle n hn) (hDrdelta n hn) (hDrdrop n hn) (hbad n)

/-- The released-clause line producer with the source kept explicit. -/
theorem hline_of_slots_sharp_var_at_jb_of_at_level_clauses_src
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {N₀ ns H : ℕ} {Hw : ℕ → ℕ}
    {g Cpre eta cRow kap M L cD delta cfirst cmax : ℝ}
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax) (hM : 0 ≤ M)
    (hconst : IsotropySlotConstants d g Cpre eta cRow kap
      (absorbedNormalizer cfirst cmax M) cD delta)
    (hFnn : ∀ j, 0 ≤ hatExcess P q N₀ j)
    (hFmono : ∀ p j : ℕ, p ≤ j → hatExcess P q N₀ j ≤ hatExcess P q N₀ p)
    {V : ℕ → ℕ → ℝ} {V0 : ℕ → ℝ} {Dr : ℕ → ℕ → ℝ} {Vmean : ℕ → ℝ}
    {bmaj : ℕ → ℝ} {beta lev : ℝ} {wv : ℕ → ℝ} {jb : ℕ → ℕ}
    {cVsum cVm : ℝ} {vsum vmsrc bsrc : ℕ → ℝ}
    (hV : ∀ n j, 0 ≤ V n j) (hV0 : ∀ n, 0 ≤ V0 n)
    (hDrnn : ∀ n j, 0 ≤ Dr n j) (hVmean0 : ∀ n, 0 ≤ Vmean n)
    (hbmaj : ∀ n, 0 ≤ bmaj n) (hbeta : 0 ≤ beta)
    (hbad : ∀ n : ℕ, Real.sqrt 2 * Real.sqrt (L + 1) *
            Response.profileBadMajorantAt 4 (bmaj n) beta lev +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((Hw n : ℕ) : ℝ)) *
            Real.sqrt (L + 1) ≤ bsrc n)
    (hH : ∀ n : ℕ, ns ≤ n → H + 1 ≤ n)
    (hHw : ∀ n : ℕ, ns ≤ n → Hw n + 1 ≤ n)
    (hjbn : ∀ n : ℕ, ns ≤ n → jb n ≤ n)
    (hmaj : ∀ n : ℕ, ns ≤ n → wv n ≤
      weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L (contrastRho g) (Hw n)
        (bmaj n) beta lev (V n) (V0 n) (Dr n) (Vmean n) ^ 2)
    (hone : ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
            (16 * (d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
          rowValue2Isotropy d cRow kap
            ((d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) + wv n) +
        2 * ((3 * (d : ℝ) + 4) *
          ((d : ℝ) *
            (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) ^ 2))
    (hVsum : ∀ n : ℕ, ns ≤ n → (∑ j ∈ Finset.range (Hw n + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V n j + V0 n)) ≤
      vsum n + cVsum * hatExcess P q N₀ (jb n))
    (hVmeanle : ∀ n : ℕ, ns ≤ n →
      Vmean n ≤ vmsrc n + cVm * hatExcess P q N₀ (jb n))
    (hDrdelta : ∀ n : ℕ, ns ≤ n → ∀ j ∈ Finset.range (Hw n + 1),
      Dr n j ≤ delta)
    (hDrdrop : ∀ n : ℕ, ns ≤ n → ∀ j ∈ Finset.range (Hw n + 1),
      Dr n j ≤ cD * (hatExcess P q N₀ (n - j) - hatExcess P q N₀ n))
    :
    ∀ n : ℕ, ns ≤ n →
      hatExcess P q N₀ n ≤
        fusionRecursionConstantIsotropySharp d Cpre eta H
            (absorbedNormalizer cfirst cmax M) L g cRow kap cD delta
            cVsum cVm *
            iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g))
              (hatExcess P q N₀) n +
          fusionRecursionConstantIsotropySharp d Cpre eta H
              (absorbedNormalizer cfirst cmax M) L g cRow kap cD delta
              cVsum cVm * hatExcess P q N₀ (jb n) ^ 2 +
            3 * weakCoefficient d Cpre *
              weakSourceGroupSummed (absorbedNormalizer cfirst cmax M) L
                (contrastRho g) (vsum n) (vmsrc n) (bsrc n) ^ 2 := by
  refine hline_of_slots_sharp_var_at_jb_at_level_src hconst hFnn hFmono hV
    hV0 hDrnn hVmean0 hbmaj hbeta hbad hH hHw hjbn ?_ hone hVsum hVmeanle
    hDrdelta hDrdrop
  intro n hn
  exact le_baseIsotropyAtPar_pinned_of_atLevel hcfirst hcmax hM
    (contrastRho_lt_one hconst.hg1) (hbmaj n) hbeta (hV n) (hV0 n) (hDrnn n)
    (hVmean0 n) (hmaj n hn)

/-- **The family block with the explicit source.** -/
theorem family_hrec_of_line_clauses_src
    {P : Measure (CoeffSpace d)}
    {q : Mat d} {N₀ ns H : ℕ} {Hw : ℕ → ℕ}
    {g Cpre eta cRow kap M L cD delta cfirst cmax : ℝ}
    (hcfirst : 0 ≤ cfirst) (hcmax : 0 ≤ cmax) (hM : 0 ≤ M)
    (hconst : IsotropySlotConstants d g Cpre eta cRow kap
      (absorbedNormalizer cfirst cmax M) cD delta)
    (hFnn : ∀ j, 0 ≤ hatExcess P q N₀ j)
    (hFmono : ∀ p j : ℕ, p ≤ j → hatExcess P q N₀ j ≤ hatExcess P q N₀ p)
    {V : ℕ → ℕ → ℕ → ℝ} {V0 : ℕ → ℕ → ℝ} {Dr : ℕ → ℕ → ℝ}
    {Vmean : ℕ → ℕ → ℝ} {bmaj : ℕ → ℝ} {beta lev : ℝ} {wv : ℕ → ℕ → ℝ}
    {cVsum cVm : ℝ} {vsum vmsrc : ℕ → ℕ → ℝ} {bsrc : ℕ → ℝ}
    (hV : ∀ m n j, 0 ≤ V m n j) (hV0 : ∀ m n, 0 ≤ V0 m n)
    (hDrnn : ∀ n j, 0 ≤ Dr n j) (hVmean0 : ∀ m n, 0 ≤ Vmean m n)
    (hbmaj : ∀ n, 0 ≤ bmaj n) (hbeta : 0 ≤ beta)
    (hbad : ∀ n : ℕ, Real.sqrt 2 * Real.sqrt (L + 1) *
            Response.profileBadMajorantAt 4 (bmaj n) beta lev +
          Real.sqrt 2 *
              (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * ((Hw n : ℕ) : ℝ)) *
            Real.sqrt (L + 1) ≤ bsrc n)
    (hH : ∀ n : ℕ, ns ≤ n → H + 1 ≤ n)
    (hHw : ∀ n : ℕ, ns ≤ n → Hw n + 1 ≤ n)
    (hmaj : ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n → wv m n ≤
      weakValueBaseIsotropyAtPar (d := d) cfirst cmax M L (contrastRho g) (Hw n)
        (bmaj n) beta lev (V m n) (V0 m n) (Dr n) (Vmean m n) ^ 2)
    (hone : ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n →
      adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1 ≤
      4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
            (16 * (d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + ((n - H : ℕ) : ℤ)) -
                adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)))) +
          rowValue2Isotropy d cRow kap
            ((d : ℝ) *
              (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) +
          wv m n) +
        2 * ((3 * (d : ℝ) + 4) *
          ((d : ℝ) *
            (adaptedHattedContrast P q ((N₀ : ℤ) + (n : ℤ)) - 1)) ^ 2))
    (hVsum : ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n →
      (∑ j ∈ Finset.range (Hw n + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V m n j + V0 m n)) ≤
      vsum m n + cVsum * hatExcess P q N₀ (min n m))
    (hVmeanle : ∀ m : ℕ, ns ≤ m → ∀ n : ℕ, ns ≤ n →
      Vmean m n ≤ vmsrc m n + cVm * hatExcess P q N₀ (min n m))
    (hDrdelta : ∀ n : ℕ, ns ≤ n → ∀ j ∈ Finset.range (Hw n + 1),
      Dr n j ≤ delta)
    (hDrdrop : ∀ n : ℕ, ns ≤ n → ∀ j ∈ Finset.range (Hw n + 1),
      Dr n j ≤ cD * (hatExcess P q N₀ (n - j) - hatExcess P q N₀ n))
    :
    ∀ n : ℕ, ns ≤ n → ∀ m : ℕ, ns ≤ m → m ≤ n →
      hatExcess P q N₀ n ≤
        fusionRecursionConstantIsotropySharp d Cpre eta H
            (absorbedNormalizer cfirst cmax M) L g cRow kap cD delta
            cVsum cVm *
            iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g))
              (hatExcess P q N₀) n +
          fusionRecursionConstantIsotropySharp d Cpre eta H
              (absorbedNormalizer cfirst cmax M) L g cRow kap cD delta
              cVsum cVm * hatExcess P q N₀ m ^ 2 +
            3 * weakCoefficient d Cpre *
              weakSourceGroupSummed (absorbedNormalizer cfirst cmax M) L
                (contrastRho g) (vsum m n) (vmsrc m n) (bsrc n) ^ 2 := by
  intro n hn m hm hmn
  have hline := hline_of_slots_sharp_var_at_jb_of_at_level_clauses_src
    (P := P) (q := q) (N₀ := N₀) (ns := ns) (H := H) (Hw := Hw)
    (jb := fun k => min k m)
    (V := V m) (V0 := V0 m) (Dr := Dr) (Vmean := Vmean m) (bmaj := bmaj)
    (beta := beta) (lev := lev) (wv := wv m)
    (vsum := vsum m) (vmsrc := vmsrc m) (bsrc := bsrc)
    hcfirst hcmax hM hconst hFnn hFmono (hV m) (hV0 m) hDrnn (hVmean0 m)
    hbmaj hbeta hbad hH hHw
    (fun k _ => min_le_left k m)
    (fun k hk => hmaj m hm k hk)
    (fun k hk => hone m hm k hk)
    (fun k hk => hVsum m hm k hk)
    (fun k hk => hVmeanle m hm k hk)
    hDrdelta hDrdrop
  have hres := hline n hn
  have hmin : min n m = m := min_eq_right hmn
  rw [hmin] at hres
  exact hres

end

end HCPolySupport.HighContrast.Quenched

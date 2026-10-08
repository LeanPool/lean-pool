/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotAlgebraAtLevel
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSplitAdapters

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSplitSupplyAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `hWsplit`/`hwsq` positions at a released threshold pair

The summed split at the paired exponents with the drop bound read at the
recursion rate, with the bad-event majorant at a free threshold pair.  The
pinned form is this at `(1 / 2, 1)`, definitionally.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The `hWsplit`/`hwsq` positions at a released threshold pair.** -/
theorem split_at_recursionAlpha_at_level
    {M L : ℝ} {Hw : ℕ} {V : ℕ → ℝ} {V0 : ℝ} {Dr : ℕ → ℝ} {Vmean : ℝ}
    {F : ℕ → ℝ} {n jb : ℕ}
    {vsum cVsum vmsrc cVm bsrc cD delta g bmaj beta lev : ℝ}
    (hFmono : ∀ p q : ℕ, p ≤ q → F q ≤ F p)
    (hM0 : 0 ≤ M) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hHw : Hw + 1 ≤ n) (hcD0 : 0 ≤ cD) (hdelta0 : 0 ≤ delta)
    (hVsum : (∑ j ∈ Finset.range (Hw + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0)) ≤
      vsum + cVsum * F jb)
    (hVmean : Vmean ≤ vmsrc + cVm * F jb)
    (hDr0 : ∀ j, 0 ≤ Dr j)
    (hDrdelta : ∀ j ∈ Finset.range (Hw + 1), Dr j ≤ delta)
    (hDr : ∀ j ∈ Finset.range (Hw + 1), Dr j ≤ cD * (F (n - j) - F n))
    (hbad : Real.sqrt 2 * Real.sqrt (L + 1) *
          Response.profileBadMajorantAt 4 bmaj beta lev +
        Real.sqrt 2 *
            (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) *
          Real.sqrt (L + 1) ≤ bsrc) :
    ∃ w : ℝ, 0 ≤ w ∧
      (16 * M * Real.sqrt L *
            ((∑ j ∈ Finset.range (Hw + 1),
                (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) * (V j + V0 + Dr j)) +
              ∑ j ∈ Finset.range (Hw + 1),
                (3 : ℝ) ^ (-(1 / 2 - contrastRho g / 2) * (j : ℝ)) *
                  Real.sqrt (2 * d * Dr j)) +
          16 * M / (2 * ((1 - contrastRho g) / 2)) *
            (Real.sqrt 2 * Real.sqrt (L + 1) *
                Response.profileBadMajorantAt 4 bmaj beta lev +
              Real.sqrt 2 *
                  (3 : ℝ) ^ (-((1 - contrastRho g) / 2) * (Hw : ℝ)) *
                Real.sqrt (L + 1)) +
          Response.constantSeminormCoefficient * (M * Real.sqrt 7 * Vmean) ≤
        weakSourceGroupSummed M L (contrastRho g) vsum vmsrc bsrc +
          weakBaseCoefficientSummed M L cVsum cVm * F jb + w) ∧
      w ^ 2 ≤ weakDropConstant (d := d) M L (contrastAlpha g) cD delta *
        iterationDropSum ((3 : ℝ) ^ (-recursionAlpha g)) F n := by
  obtain ⟨w, hw0, hbase, hwsq⟩ :=
    weakValueSharpMajorant_le_three_group_summed_at_level (d := d) hFmono hM0
      (contrastRho_lt_one hg1) (contrastAlpha_pos hg1)
      (contrastAlpha_le_half hg0) (rooted_weight_eq_contrastAlpha g) hHw
      hcD0 hdelta0 hVsum hVmean hDr0 hDrdelta hDr hbad
  exact ⟨w, hw0, hbase,
    hwsq_at_recursionAlpha hFmono (le_of_lt hg1) (contrastAlpha_pos hg1) hcD0
      hdelta0 hwsq⟩

end

end HCPolySupport.HighContrast.Quenched

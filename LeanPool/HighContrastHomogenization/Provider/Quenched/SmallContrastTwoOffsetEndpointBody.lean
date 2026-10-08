/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOffsetDecayToOrigin
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRestartEndpoint

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastTwoOffsetEndpointBody

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `hcore` body from a decay at any offset

The endpoint's tail does not care *where* the geometric decay starts: the offset
joins the prefactor, and the prefactor is what `hpref` already carries into a
law-free exponent.  Stating that once, at a free offset, isolates the route's
one open step.

With this in place the offset route reduces to a single missing lemma — the
two-offset iteration, whose recursion is available only from a second offset
`n₀ ≥ ns` while the family reports its quadratic index at `shiftedBaseIndex ns`
(the two-offset admissibility condition).  Everything above and below it is
already proved.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The `hcore` body from a decay at any offset.** -/
theorem hcore_body_of_two_offset_decay
    {P : Measure (CoeffSpace d)} {q : Mat d} {N₀ n₀ : ℕ} {Kpre gam : ℝ}
    (hgam0 : 0 < gam) (hgam1 : gam ≤ 1) (hKpre0 : 0 ≤ Kpre)
    (hFnn : ∀ n : ℕ, 0 ≤ hatExcess P q N₀ n)
    (hFmono : ∀ m n : ℕ, m ≤ n → hatExcess P q N₀ n ≤ hatExcess P q N₀ m)
    (hdecay : ∀ n : ℕ, n₀ ≤ n →
      hatExcess P q N₀ n ≤ Kpre * ((3 : ℝ) ^ (-gam)) ^ (n - n₀))
    {base Centry Cpref : ℝ} (hbase : 3 ≤ base) (hCpref : 0 ≤ Cpref)
    (hentry : (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base Centry)
    (hpref : 9 / 2 *
        ((Kpre + hatExcess P q N₀ 0) * (3 : ℝ) ^ (gam * (n₀ : ℝ))) *
        (Real.rpow (3 : ℝ) (gam / 2) + 1) ≤ Real.rpow base Cpref)
    (htransfer : ∀ m : ℕ, 2 * N₀ ≤ m →
      annealedContrast P (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast P q
            (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1)) +
          9 / 2 *
            ((Kpre + hatExcess P q N₀ 0) * (3 : ℝ) ^ (gam * (n₀ : ℝ))) *
            Real.rpow (3 : ℝ)
              (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ))) :
    ∃ m₀ : ℕ,
      (3 : ℝ) ^ m₀ ≤ Real.rpow base (Centry + (1 + Cpref / (gam / 2))) ∧
        ∀ j : ℕ, annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
          Real.rpow (3 : ℝ) (-(gam / 2) * (j : ℝ)) := by
  have horigin := hatted_decay_of_offset_decay hgam0 hKpre0 hFnn hFmono hdecay
  have hKpre : (0 : ℝ) ≤
      (Kpre + hatExcess P q N₀ 0) * (3 : ℝ) ^ (gam * (n₀ : ℝ)) := by
    have hsum : (0 : ℝ) ≤ Kpre + hatExcess P q N₀ 0 := by
      have := hFnn 0
      linarith only [hKpre0, this]
    exact mul_nonneg hsum (Real.rpow_pos_of_pos (by norm_num) _).le
  exact hcore_body_of_hatted_decay hKpre hgam0 hgam1 horigin hbase hCpref
    hentry hpref htransfer

end

end HCPolySupport.HighContrast.Quenched

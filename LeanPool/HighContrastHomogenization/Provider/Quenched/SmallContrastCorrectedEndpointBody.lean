/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastLinearDecay
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTwoOffsetEndpointBody

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCorrectedEndpointBody

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `hcore` body from the corrected family clause

the join.  From the corrected family clause of
the strengthened free-threshold estimate — the `∀ (n,m)` recursion with the three-channel
source model whose Π-carrying channel decays ABSOLUTELY at the anchor
scale — the linear level-schedule descent (`linear_descent_hdecay`) delivers
`hdecay` at the law-free rate `linRate` from the linear start `linR … 0`,
and the proved tail (`hcore_body_of_two_offset_decay`, the corresponding clause)
carries it to the `hcore` body: the threshold in
`base^(Centry + (1 + Cpref/(linRate/2)))` and the contrast decay at
`linRate/2`, prefactor one.

The two `h`-prefixed clause hypotheses (`hfam`, `hsrc`) are the corrected
provider's interface: their discharge from the frozen premises is the
free-threshold variance supply at the released carriers — the quenched
quenched realization of the strengthened free-threshold estimate.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The `hcore` body from the corrected family clause.** -/
theorem hcore_body_of_corrected_family
    {P : Measure (CoeffSpace d)} {q : Mat d} {N₀ : ℕ}
    {A alpha d0 S0 S1 S2 b0 bA b2 : ℝ} {src : ℕ → ℕ → ℝ} {ns cA : ℕ}
    (hA : 1 ≤ A) (halpha : 0 < alpha)
    (hcA : 24 * A ≤ (3 : ℝ) ^ (alpha * (cA : ℝ)))
    (hd0 : 0 < d0) (hgs3 : (128 * A ^ 2) ^ 3 * d0 ≤ 1 / 3)
    (hS0 : 1 ≤ S0) (hS1 : 1 ≤ S1) (hS2 : 1 ≤ S2)
    (hb0 : 0 < b0) (hbA : 0 < bA) (hb2 : 0 < b2)
    (hFnn : ∀ n : ℕ, 0 ≤ hatExcess P q N₀ n)
    (hFmono : ∀ m n : ℕ, m ≤ n → hatExcess P q N₀ n ≤ hatExcess P q N₀ m)
    (hFd0 : ∀ n, hatExcess P q N₀ n ≤ d0)
    (hfam : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      hatExcess P q N₀ n ≤
        A * iterationDropSum ((3 : ℝ) ^ (-alpha)) (hatExcess P q N₀) n +
          A * hatExcess P q N₀ m ^ 2 + src n m)
    (hsrc : ∀ n m : ℕ, ns ≤ m → m ≤ n →
      src n m ≤ S1 * (3 : ℝ) ^ (-(bA * (m : ℝ))) +
        S0 * (3 : ℝ) ^ (-(b0 * ((n - m : ℕ) : ℝ))) +
        S2 * (3 : ℝ) ^ (-(b2 * (n : ℝ))))
    {base Centry Cpref : ℝ} (hbase : 3 ≤ base) (hCpref : 0 ≤ Cpref)
    (hentry : (3 : ℝ) ^ (2 * N₀) ≤ Real.rpow base Centry)
    (hpref : 9 / 2 *
        ((1 + hatExcess P q N₀ 0) *
          (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
            ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) *
        (Real.rpow (3 : ℝ) (linRate A alpha b0 bA b2 cA S0 / 2) + 1) ≤
      Real.rpow base Cpref)
    (htransfer : ∀ m : ℕ, 2 * N₀ ≤ m →
      annealedContrast P (m : ℤ) - 1 ≤
        (9 / 2 : ℝ) * ((d : ℝ) *
          (adaptedHattedContrast P q
            (Prop42Scalar.correctedTiltScale N₀ m : ℤ) - 1)) +
          9 / 2 *
            ((1 + hatExcess P q N₀ 0) *
              (3 : ℝ) ^ (linRate A alpha b0 bA b2 cA S0 *
                ((linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 : ℕ) : ℝ))) *
            Real.rpow (3 : ℝ)
              (-((m - Prop42Scalar.correctedTiltScale N₀ m : ℕ) : ℝ))) :
    ∃ m₀ : ℕ,
      (3 : ℝ) ^ m₀ ≤ Real.rpow base (Centry +
          (1 + Cpref / (linRate A alpha b0 bA b2 cA S0 / 2))) ∧
        ∀ j : ℕ, annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
          Real.rpow (3 : ℝ)
            (-(linRate A alpha b0 bA b2 cA S0 / 2) * (j : ℝ)) := by
  obtain ⟨hrate0, hrate1, _hthresh, hdec⟩ :=
    linear_descent_hdecay (src := src) (ns := ns) (cA := cA)
      hA halpha hcA hd0 hgs3 hS0 hS1 hS2 hb0 hbA hb2
      hFnn (fun p q' hpq => hFmono p q' hpq) hFd0 hfam hsrc
  have hdecay : ∀ n : ℕ,
      linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0 ≤ n →
      hatExcess P q N₀ n ≤
        1 * ((3 : ℝ) ^ (-(linRate A alpha b0 bA b2 cA S0))) ^
          (n - linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0) := by
    intro n hn
    rw [one_mul]
    exact hdec n hn
  exact hcore_body_of_two_offset_decay
    (n₀ := linR ns cA A alpha b0 bA b2 S0 S1 S2 d0 0)
    hrate0 hrate1 zero_le_one hFnn hFmono hdecay hbase hCpref hentry
    hpref htransfer

end

end HCPolySupport.HighContrast.Quenched

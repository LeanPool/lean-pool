/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecenteredCertificates
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSkewLaw

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCarryBack

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Carrying the `hcore` body back from the recentered law stage 2b, bottom. put the four isotropy
certificates at the
recentered block `E'`, at the cost of running the account at
`recenteredLaw P hg` rather than at `P`.  This file pays that cost back.

The `hcore` conclusion speaks only of `annealedContrast`, and's
`annealedContrast_recenteredLaw` says that quantity is **invariant** under
recentering.  So the carry-back is a rewrite under the `∀ j`, with no loss:
the delay bound `3 ^ m₀ ≤ base ^ Cdelay` does not mention the law at all, and
the decay bound transports pointwise.

With the top and this bottom half, the recentered route is complete: what
remains is the instantiation in between.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The carry-back.**  The `hcore` inner body at the recentered law is the
`hcore` inner body at the original law. -/
theorem hcore_body_carry_back [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : Mat d} (hg : IsSkewMat g)
    (hint : ∀ m : ℤ, HasFiniteAdaptedMean P (1 : Mat d) m)
    (hpd : ∀ m : ℤ, BlockPosDef (annealedBlock P (centeredCube d m)))
    {base Cdelay alpha : ℝ}
    (h : ∃ m₀ : ℕ, (3 : ℝ) ^ m₀ ≤ Real.rpow base Cdelay ∧
      ∀ j : ℕ, annealedContrast (recenteredLaw P hg) ((m₀ + j : ℕ) : ℤ) - 1 ≤
        Real.rpow (3 : ℝ) (-alpha * (j : ℝ))) :
    ∃ m₀ : ℕ, (3 : ℝ) ^ m₀ ≤ Real.rpow base Cdelay ∧
      ∀ j : ℕ, annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
        Real.rpow (3 : ℝ) (-alpha * (j : ℝ)) := by
  obtain ⟨m₀, hm₀, hdecay⟩ := h
  refine ⟨m₀, hm₀, fun j => ?_⟩
  have hj := hdecay j
  rwa [annealedContrast_recenteredLaw ((m₀ + j : ℕ) : ℤ)
    (hint _) (hpd _) hg] at hj

end

end HCPolySupport.HighContrast.Quenched

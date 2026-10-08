/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedCoupledWitness

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedEndgameExponent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The endgame exponent of the quenched mixing scale

The concentration exponent `μ = d/2 - g` of the stopping construction in
`ss.random.dirichlet` is positive on the whole
admissible range and doubles to the stretched exponent `d - 2g` of the
homogenization-scale tail.  This file records that identification and delivers
the coupled mixing-scale witness with the exponent written in the shape the
homogenization statement uses.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open Book.Ch05.Section57

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The coupled mixing-scale witness with the stretched exponent written as the
homogenization statement writes it. -/
theorem exists_coupled_mixingScale_at_exponent
    {P : Measure Ω} [IsProbabilityMeasure P]
    {nstar qfb b : ℕ} {R B F : ℕ → Ω → ℝ}
    {theta mu eta cd delta Cblk : ℝ}
    (htheta : 0 < theta) (hmu : 0 < mu) (heta : eta = 2 * mu) (hcd : 0 < cd)
    (hdelta : 0 < delta) (hCblk : 0 < Cblk)
    (hFmeas : ∀ n, Measurable (F n))
    (hRtail : ∀ n q : ℕ, nstar ≤ n →
      P.real {ω | (3 : ℝ) ^ (n + q + b) < R n ω} ≤
        Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))))
    (hBdecay : ∀ᵐ ω ∂P, ∀ (m : ℕ), nstar ≤ m →
      B m ω ≤ Cblk * delta *
        (3 : ℝ) ^ (-theta *
          ((m : ℝ) - (stoppingGeneration nstar qfb R m ω : ℝ) - (nstar : ℝ))))
    (hFsum : ∀ᵐ ω ∂P, ∀ k : ℕ,
      HasSum (fun j : ℕ => (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (k + j) ω)
        (F k ω))
    {N0 : ℕ} {Bconst : ℝ} (hstar : nstar ≤ N0) (hBconst : 1 ≤ Bconst)
    (hN0low : (qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk ≤
      (N0 : ℝ) - (nstar : ℝ))
    (hN0gain : Real.log 2 ≤
      cd * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)) * ((3 : ℝ) ^ (mu / 2) - 1))
    (hN0abs : 2 * Real.log 4 ≤
      cd * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)))
    (hBrel : (3 : ℝ) ^ (2 * mu *
        ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ))) ≤
      cd / 2 * Bconst ^ (2 * mu)) :
    ∃ (Amix : ℝ) (Rmix : Ω → ℝ),
      Amix = 3 * (3 : ℝ) ^ N0 * Bconst ∧
      1 ≤ Amix ∧
      Measurable Rmix ∧
      (∀ ω, 1 ≤ Rmix ω) ∧
      (∀ t : ℝ, 1 ≤ t →
        P.real {ω | 2 * t ≤ Rmix ω} ≤ Real.exp (-1 * t ^ eta)) ∧
      (∀ n : ℕ, MeasurableSet (rowBadEvent delta F n)) ∧
      (∀ (n : ℕ) (ω : Ω), ω ∈ rowBadEvent delta F n ↔ delta ≤ F n ω) ∧
      (∀ᵐ ω ∂P, ∀ n : ℕ,
        Amix * Rmix ω ≤ (3 : ℝ) ^ n → ω ∉ rowBadEvent delta F n) := by
  subst heta
  exact exists_coupled_mixingScale_of_rowSeries htheta hmu hcd hdelta hCblk
    hFmeas hRtail hBdecay hFsum hstar hBconst hN0low hN0gain hN0abs hBrel

end

end Quenched
end HighContrast
end HCPolySupport

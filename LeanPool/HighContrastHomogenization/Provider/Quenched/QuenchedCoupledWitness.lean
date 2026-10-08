/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedBadTail

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedCoupledWitness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coupled mixing-scale witness of the quenched endgame

The normalized mixing scale of `e.random.final.scale` is
selected together with the pathwise certificate that belongs to that same scale:
the marginal tail and the all-later absence of bad events refer to one function,
so a consumer cannot substitute another random variable with the same marginal
law.  The stretched exponent is the one carried by the finite-range gauge.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open Book.Ch05.Section57

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- One mixing scale, its stretched-exponential marginal tail, and its own
all-later certificate against the bad events of the weighted row series. -/
theorem exists_coupled_mixingScale_of_rowSeries
    {P : Measure Ω} [IsProbabilityMeasure P]
    {nstar qfb b : ℕ} {R B F : ℕ → Ω → ℝ} {theta mu cd delta Cblk : ℝ}
    (htheta : 0 < theta) (hmu : 0 < mu) (hcd : 0 < cd)
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
        P.real {ω | 2 * t ≤ Rmix ω} ≤ Real.exp (-1 * t ^ (2 * mu))) ∧
      (∀ n : ℕ, MeasurableSet (rowBadEvent delta F n)) ∧
      (∀ (n : ℕ) (ω : Ω), ω ∈ rowBadEvent delta F n ↔ delta ≤ F n ω) ∧
      (∀ᵐ ω ∂P, ∀ n : ℕ,
        Amix * Rmix ω ≤ (3 : ℝ) ^ n → ω ∉ rowBadEvent delta F n) := by
  have hBadMeas : ∀ n : ℕ, MeasurableSet (rowBadEvent delta F n) :=
    fun n => measurableSet_rowBadEvent hFmeas delta n
  have heta : (0 : ℝ) < 2 * mu := by linarith only [hmu]
  have htail : ∀ N : ℕ, N0 ≤ N →
      P.real (badTailEvent (rowBadEvent delta F) N) ≤
        Real.exp (-((3 : ℝ) ^ (((N - N0 : ℕ) : ℝ)) / Bconst) ^ (2 * mu)) :=
    fun N hN => measureReal_badTailEvent_rowBadEvent_le htheta hmu hcd hdelta
      hCblk hRtail hBdecay hFsum hstar hBconst hN0low hN0gain hN0abs hBrel N hN
  obtain ⟨Rmix, hmeas, hone, hRtailMix, -, hcert⟩ :=
    exists_normalized_quenchedMinimalScale_of_badTailEvent_bound
      (P := P) (N0 := N0) (Bad := rowBadEvent delta F) (B := Bconst)
      (eta := 2 * mu) hBadMeas heta hBconst htail
  refine ⟨3 * (3 : ℝ) ^ N0 * Bconst, Rmix, rfl, ?_, hmeas, hone, ?_,
    hBadMeas, fun _ _ => Iff.rfl, hcert⟩
  · have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ N0 := one_le_pow₀ (by norm_num)
    nlinarith only [hpow, hBconst]
  · intro t ht
    have := hRtailMix t ht
    rwa [neg_one_mul]

end

end Quenched
end HighContrast
end HCPolySupport

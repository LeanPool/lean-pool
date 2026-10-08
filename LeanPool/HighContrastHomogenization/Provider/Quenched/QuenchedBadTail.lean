/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedGenerationTail
public import LeanPool.HighContrastHomogenization.Provider.Quenched.NormalizedMinimalScale

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedBadTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bad-tail estimate of the quenched endgame

Summing the one-generation estimate over all later generations produces the
endpoint-safe radius of `e.random.final.scale` in the form
consumed by the abstract normalized minimal scale: a stretched-exponential bound
for the bad-tail event whose exponent is exactly the one carried by the
finite-range gauge.  The last theorem selects the normalized mixing scale of
`e.random.final.scale` together with the pathwise
certificate belonging to that same scale.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open Book.Ch05.Section57

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The per-generation exponent of the bad-tail estimate. -/
@[expose]
public def badTailExponent (nstar : ℕ) (theta mu cd Cblk : ℝ) (qfb b n : ℕ) :
    ℝ :=
  cd * (3 : ℝ) ^ (2 * mu *
    ((n : ℝ) - (nstar : ℝ) - badTailOffset theta Cblk qfb b))

private theorem badTailExponent_pos {nstar : ℕ} {theta mu cd Cblk : ℝ}
    (hcd : 0 < cd) (qfb b n : ℕ) :
    0 < badTailExponent nstar theta mu cd Cblk qfb b n :=
  mul_pos hcd (Real.rpow_pos_of_pos (by norm_num) _)

private theorem badTailExponent_mono {nstar : ℕ} {theta mu cd Cblk : ℝ}
    (hmu : 0 < mu) (hcd : 0 < cd) (qfb b : ℕ) {n n' : ℕ} (hn : n ≤ n') :
    badTailExponent nstar theta mu cd Cblk qfb b n ≤
      badTailExponent nstar theta mu cd Cblk qfb b n' := by
  have hcast : (n : ℝ) ≤ (n' : ℝ) := Nat.cast_le.2 hn
  have hexp : 2 * mu * ((n : ℝ) - (nstar : ℝ) -
      badTailOffset theta Cblk qfb b) ≤
      2 * mu * ((n' : ℝ) - (nstar : ℝ) - badTailOffset theta Cblk qfb b) :=
    mul_le_mul_of_nonneg_left (by linarith only [hcast])
      (by linarith only [hmu])
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hcd.le

/-- The bad-tail event of the weighted row series obeys the stretched-exponential
bound in the shape consumed by the abstract normalized minimal scale. -/
theorem measureReal_badTailEvent_rowBadEvent_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {nstar qfb b : ℕ} {R B F : ℕ → Ω → ℝ} {theta mu cd delta Cblk : ℝ}
    (htheta : 0 < theta) (hmu : 0 < mu) (hcd : 0 < cd)
    (hdelta : 0 < delta) (hCblk : 0 < Cblk)
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
      badTailExponent nstar theta mu cd Cblk qfb b N0 * ((3 : ℝ) ^ (mu / 2) - 1))
    (hN0abs : 2 * Real.log 4 ≤
      badTailExponent nstar theta mu cd Cblk qfb b N0)
    (hBrel : (3 : ℝ) ^ (2 * mu *
        ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ))) ≤
      cd / 2 * Bconst ^ (2 * mu))
    (N : ℕ) (hN : N0 ≤ N) :
    P.real (badTailEvent (rowBadEvent delta F) N) ≤
      Real.exp (-((3 : ℝ) ^ (((N - N0 : ℕ) : ℝ)) / Bconst) ^ (2 * mu)) := by
  set c2 : ℝ := badTailOffset theta Cblk qfb b with hc2
  set A : ℕ → ℝ := fun n => badTailExponent nstar theta mu cd Cblk qfb b n
    with hA
  have hApos : ∀ n, 0 < A n := fun n => badTailExponent_pos hcd qfb b n
  have hAmono : ∀ n n' : ℕ, n ≤ n' → A n ≤ A n' :=
    fun _ _ h => badTailExponent_mono hmu hcd qfb b h
  have hBconstPos : (0 : ℝ) < Bconst := lt_of_lt_of_le zero_lt_one hBconst
  -- the one-generation estimate at every later generation
  have hgen : ∀ k : ℕ,
      P.real (rowBadEvent delta F (N + k)) ≤ 2 * Real.exp (-(A (N + k))) := by
    intro k
    have hNk : N0 ≤ N + k := le_trans hN (Nat.le_add_right N k)
    have hcastNk : (N0 : ℝ) ≤ ((N + k : ℕ) : ℝ) := Nat.cast_le.2 hNk
    have hlow : (qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk ≤
        ((N + k : ℕ) : ℝ) - (nstar : ℝ) := by
      linarith only [hN0low, hcastNk]
    have hgainStep : Real.log 2 ≤ A (N + k) * ((3 : ℝ) ^ (mu / 2) - 1) := by
      have hone : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ (mu / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hmu])
      rw [Real.rpow_zero] at hone
      have hmono := hAmono N0 (N + k) hNk
      have hfac : (0 : ℝ) ≤ (3 : ℝ) ^ (mu / 2) - 1 := by linarith only [hone]
      exact le_trans hN0gain (mul_le_mul_of_nonneg_right hmono hfac)
    exact measureReal_rowBadEvent_le htheta hmu hcd hdelta hCblk hRtail hBdecay
      hFsum (le_trans hstar hNk) hlow hgainStep
  -- the later generations form a super-geometric family
  have hAsplit : ∀ k : ℕ, A (N + k) = A N * (3 : ℝ) ^ (2 * mu * (k : ℝ)) := by
    intro k
    have hcast : ((N + k : ℕ) : ℝ) = (N : ℝ) + (k : ℝ) := by push_cast; ring
    rw [hA]
    simp only [badTailExponent, ← hc2, hcast]
    rw [show 2 * mu * ((N : ℝ) + (k : ℝ) - (nstar : ℝ) - c2) =
        2 * mu * ((N : ℝ) - (nstar : ℝ) - c2) + 2 * mu * (k : ℝ) by ring,
      Real.rpow_add (by norm_num)]
    ring
  have hnu : (0 : ℝ) < 2 * mu := by linarith only [hmu]
  have hsummableExp :
      Summable fun k : ℕ =>
        2 * Real.exp (-(A N * (3 : ℝ) ^ (2 * mu * (k : ℝ)))) :=
    (summable_exp_neg_triadic (hApos N) hnu).mul_left _
  have hgenSplit : ∀ k : ℕ,
      P.real (rowBadEvent delta F (N + k)) ≤
        2 * Real.exp (-(A N * (3 : ℝ) ^ (2 * mu * (k : ℝ)))) := by
    intro k
    have := hgen k
    rwa [hAsplit k] at this
  have hsummable : Summable fun k : ℕ => P.real (rowBadEvent delta F (N + k)) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) hgenSplit
      hsummableExp
  -- the union bound over generations
  have hunion : P.real (badTailEvent (rowBadEvent delta F) N) ≤
      ∑' k : ℕ, P.real (rowBadEvent delta F (N + k)) :=
    measureReal_badTailEvent_le_tsum_shift hsummable
  have houterGain : Real.log 2 ≤ A N * ((3 : ℝ) ^ (2 * mu) - 1) := by
    have hstep : (3 : ℝ) ^ (mu / 2) ≤ (3 : ℝ) ^ (2 * mu) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hmu])
    have hone : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ (mu / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hmu])
    rw [Real.rpow_zero] at hone
    have hmono := hAmono N0 N hN
    have hfac : (0 : ℝ) ≤ (3 : ℝ) ^ (mu / 2) - 1 := by linarith only [hone]
    have hchain : A N0 * ((3 : ℝ) ^ (mu / 2) - 1) ≤
        A N * ((3 : ℝ) ^ (2 * mu) - 1) := by
      have h1 : A N0 * ((3 : ℝ) ^ (mu / 2) - 1) ≤
          A N * ((3 : ℝ) ^ (mu / 2) - 1) :=
        mul_le_mul_of_nonneg_right hmono hfac
      have h2 : A N * ((3 : ℝ) ^ (mu / 2) - 1) ≤
          A N * ((3 : ℝ) ^ (2 * mu) - 1) :=
        mul_le_mul_of_nonneg_left (by linarith only [hstep]) (hApos N).le
      exact le_trans h1 h2
    exact le_trans hN0gain hchain
  have htsum : ∑' k : ℕ, P.real (rowBadEvent delta F (N + k)) ≤
      4 * Real.exp (-(A N)) := by
    have hcmp := hsummable.tsum_le_tsum hgenSplit hsummableExp
    have hgeom : ∑' k : ℕ,
        2 * Real.exp (-(A N * (3 : ℝ) ^ (2 * mu * (k : ℝ)))) ≤
          4 * Real.exp (-(A N)) := by
      rw [tsum_mul_left]
      have := tsum_exp_neg_triadic_le_two_mul (A := A N) (nu := 2 * mu)
        (hApos N).le hnu.le houterGain
      calc
        2 * ∑' k : ℕ, Real.exp (-(A N * (3 : ℝ) ^ (2 * mu * (k : ℝ))))
            ≤ 2 * (2 * Real.exp (-(A N))) := by
          exact mul_le_mul_of_nonneg_left this (by norm_num)
        _ = 4 * Real.exp (-(A N)) := by ring
    exact le_trans hcmp hgeom
  -- absorb the multiplicity and match the consumed shape
  have habs : 2 * Real.log 4 ≤ A N := le_trans hN0abs (hAmono N0 N hN)
  have hhalf : 4 * Real.exp (-(A N)) ≤ Real.exp (-(A N / 2)) :=
    mul_exp_neg_le_exp_neg_half (by norm_num) habs
  have hshape : ((3 : ℝ) ^ (((N - N0 : ℕ) : ℝ)) / Bconst) ^ (2 * mu) ≤
      A N / 2 := by
    have hcastN : ((N - N0 : ℕ) : ℝ) = (N : ℝ) - (N0 : ℝ) := by
      rw [Nat.cast_sub hN]
    have hYpos : (0 : ℝ) < Bconst ^ (2 * mu) :=
      Real.rpow_pos_of_pos hBconstPos _
    have hZpos : (0 : ℝ) <
        (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (nstar : ℝ) - c2)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hdiv : ((3 : ℝ) ^ (((N - N0 : ℕ) : ℝ)) / Bconst) ^ (2 * mu) =
        (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (N0 : ℝ))) / Bconst ^ (2 * mu) := by
      rw [Real.div_rpow (Real.rpow_nonneg (by norm_num) _) hBconstPos.le,
        hcastN, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      rw [show ((N : ℝ) - (N0 : ℝ)) * (2 * mu) = 2 * mu * ((N : ℝ) - (N0 : ℝ))
        by ring]
    have hANhalf : A N / 2 =
        cd / 2 * (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (nstar : ℝ) - c2)) := by
      rw [hA]
      simp only [badTailExponent, ← hc2]
      ring
    rw [hdiv, hANhalf, div_le_iff₀ hYpos]
    have hprod : (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + c2 - (N0 : ℝ))) *
        (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (nstar : ℝ) - c2)) =
        (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (N0 : ℝ))) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have hstepMul :
        (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + c2 - (N0 : ℝ))) *
            (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (nstar : ℝ) - c2)) ≤
          cd / 2 * Bconst ^ (2 * mu) *
            (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (nstar : ℝ) - c2)) :=
      mul_le_mul_of_nonneg_right (by rw [hc2]; exact hBrel) hZpos.le
    rw [hprod] at hstepMul
    calc
      (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (N0 : ℝ)))
          ≤ cd / 2 * Bconst ^ (2 * mu) *
            (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (nstar : ℝ) - c2)) := hstepMul
      _ = cd / 2 * (3 : ℝ) ^ (2 * mu * ((N : ℝ) - (nstar : ℝ) - c2)) *
            Bconst ^ (2 * mu) := by ring
  have hfinal : Real.exp (-(A N / 2)) ≤
      Real.exp (-((3 : ℝ) ^ (((N - N0 : ℕ) : ℝ)) / Bconst) ^ (2 * mu)) :=
    Real.exp_le_exp.mpr (neg_le_neg hshape)
  exact le_trans hunion (le_trans htsum (le_trans hhalf hfinal))

end

end Quenched
end HighContrast
end HCPolySupport

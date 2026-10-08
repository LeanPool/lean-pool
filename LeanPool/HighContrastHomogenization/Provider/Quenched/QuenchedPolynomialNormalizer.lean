/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedEndgameExponent

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedPolynomialNormalizer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The polynomial cost of the mixing normalizer

The normalizer of the mixing scale is the product of the base generation and the
gauge normalizer.  Its polynomial cost is additive in the exponents, exactly as
the reference length of the homogenization statement is: three separate
exponents are useless, their sum is what must be admissible.  This file records
that absorption, the resulting mixing-scale witness carrying its own polynomial
bound, and an explicit admissible pair for which the two constituent bounds are
checkable.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory
open Book.Ch05.Section57

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Additive absorption of the three polynomial costs -/

/-- The three polynomial costs of the mixing normalizer are absorbed by the sum
of their exponents; requiring each separately is not enough. -/
theorem three_mul_pow_mul_le_rpow {base Bconst C1 C2 C3 Cmix : ℝ} {N0 : ℕ}
    (hbase : 1 ≤ base) (hBnonneg : 0 ≤ Bconst)
    (hthree : (3 : ℝ) ≤ base ^ C3)
    (hgen : (3 : ℝ) ^ N0 ≤ base ^ C1)
    (hnorm : Bconst ≤ base ^ C2)
    (hsum : C1 + C2 + C3 ≤ Cmix) :
    3 * (3 : ℝ) ^ N0 * Bconst ≤ base ^ Cmix := by
  have hbase0 : (0 : ℝ) < base := lt_of_lt_of_le zero_lt_one hbase
  have hC1 : (0 : ℝ) < base ^ C1 := Real.rpow_pos_of_pos hbase0 _
  have hC3 : (0 : ℝ) < base ^ C3 := Real.rpow_pos_of_pos hbase0 _
  have hgen0 : (0 : ℝ) ≤ (3 : ℝ) ^ N0 := by positivity
  have hstep1 : 3 * (3 : ℝ) ^ N0 * Bconst ≤ base ^ C3 * base ^ C1 * base ^ C2 := by
    have h1 : 3 * (3 : ℝ) ^ N0 ≤ base ^ C3 * base ^ C1 :=
      mul_le_mul hthree hgen hgen0 hC3.le
    exact mul_le_mul h1 hnorm hBnonneg (by positivity)
  have hcollect : base ^ C3 * base ^ C1 * base ^ C2 = base ^ (C1 + C2 + C3) := by
    rw [← Real.rpow_add hbase0, ← Real.rpow_add hbase0]
    ring_nf
  rw [hcollect] at hstep1
  exact hstep1.trans (Real.rpow_le_rpow_of_exponent_le hbase hsum)

/-! ## The mixing-scale witness with its polynomial cost -/

/-- The coupled mixing-scale witness together with the polynomial bound on its
normalizer required by the physical-scale assembly. -/
theorem exists_coupled_mixingScale_polynomial
    {P : Measure Ω} [IsProbabilityMeasure P]
    {nstar qfb b : ℕ} {R B F : ℕ → Ω → ℝ}
    {theta mu eta cd delta Cblk : ℝ} {base C1 C2 C3 Cmix : ℝ}
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
      cd / 2 * Bconst ^ (2 * mu))
    (hbase : 1 ≤ base) (hthree : (3 : ℝ) ≤ base ^ C3)
    (hgen : (3 : ℝ) ^ N0 ≤ base ^ C1) (hnorm : Bconst ≤ base ^ C2)
    (hsum : C1 + C2 + C3 ≤ Cmix) :
    ∃ (Amix : ℝ) (Rmix : Ω → ℝ),
      1 ≤ Amix ∧
      Amix ≤ base ^ Cmix ∧
      Measurable Rmix ∧
      (∀ ω, 1 ≤ Rmix ω) ∧
      (∀ t : ℝ, 1 ≤ t →
        P.real {ω | 2 * t ≤ Rmix ω} ≤ Real.exp (-1 * t ^ eta)) ∧
      (∀ n : ℕ, MeasurableSet (rowBadEvent delta F n)) ∧
      (∀ (n : ℕ) (ω : Ω), ω ∈ rowBadEvent delta F n ↔ delta ≤ F n ω) ∧
      (∀ᵐ ω ∂P, ∀ n : ℕ,
        Amix * Rmix ω ≤ (3 : ℝ) ^ n → ω ∉ rowBadEvent delta F n) := by
  obtain ⟨Amix, Rmix, hdef, hone, hmeas, hlow, htail, hbadmeas, hiff, hcert⟩ :=
    exists_coupled_mixingScale_at_exponent htheta hmu heta hcd hdelta hCblk
      hFmeas hRtail hBdecay hFsum hstar hBconst hN0low hN0gain hN0abs hBrel
  refine ⟨Amix, Rmix, hone, ?_, hmeas, hlow, htail, hbadmeas, hiff, hcert⟩
  rw [hdef]
  exact three_mul_pow_mul_le_rpow hbase
    (le_trans zero_le_one hBconst) hthree hgen hnorm hsum

/-! ## An explicit admissible pair -/

/-- The explicit real threshold above which a base generation meets the three
lower bounds of the bad-tail estimate. -/
@[expose]
def admissibleGenerationBound (nstar qfb b : ℕ) (theta mu cd Cblk : ℝ) : ℝ :=
  max (max ((nstar : ℝ))
        ((nstar : ℝ) + ((qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk)))
    ((nstar : ℝ) + badTailOffset theta Cblk qfb b +
      (max (Real.log 2 / ((3 : ℝ) ^ (mu / 2) - 1)) (2 * Real.log 4) / cd - 1) /
        (2 * mu * Real.log 3))

/-- The explicit normalizer attached to a base generation. -/
@[expose]
def normalizerWitness (mu cd Z : ℝ) : ℝ :=
  max 1 ((2 / cd * Z) ^ (1 / (2 * mu)))

theorem one_le_normalizerWitness (mu cd Z : ℝ) : 1 ≤ normalizerWitness mu cd Z :=
  le_max_left _ _

/-- The explicit normalizer absorbs its own positive datum. -/
theorem le_mul_normalizerWitness {mu cd Z : ℝ} (hmu : 0 < mu) (hcd : 0 < cd)
    (hZ : 0 < Z) :
    Z ≤ cd / 2 * normalizerWitness mu cd Z ^ (2 * mu) := by
  have hpos : 0 < 2 / cd * Z := by positivity
  have hmu2 : (0 : ℝ) < 2 * mu := by linarith only [hmu]
  have hWpos : 0 < (2 / cd * Z) ^ (1 / (2 * mu)) := Real.rpow_pos_of_pos hpos _
  have hbase : ((2 / cd * Z) ^ (1 / (2 * mu))) ^ (2 * mu) = 2 / cd * Z := by
    rw [← Real.rpow_mul hpos.le, one_div_mul_cancel (ne_of_gt hmu2), Real.rpow_one]
  have hmono : ((2 / cd * Z) ^ (1 / (2 * mu))) ^ (2 * mu) ≤
      normalizerWitness mu cd Z ^ (2 * mu) :=
    Real.rpow_le_rpow hWpos.le (le_max_right _ _) hmu2.le
  rw [hbase] at hmono
  have hval : cd / 2 * (2 / cd * Z) = Z := by field_simp
  calc
    Z = cd / 2 * (2 / cd * Z) := hval.symm
    _ ≤ cd / 2 * normalizerWitness mu cd Z ^ (2 * mu) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)

/-- An admissible base generation and normalizer, both with an explicit upper
bound, so that their polynomial costs can be checked. -/
theorem exists_admissible_thresholds_bounded {nstar qfb b : ℕ}
    {theta mu cd Cblk : ℝ} (hmu : 0 < mu) (hcd : 0 < cd) :
    ∃ (N0 : ℕ) (Bconst : ℝ),
      nstar ≤ N0 ∧ 1 ≤ Bconst ∧
      (qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk ≤
        (N0 : ℝ) - (nstar : ℝ) ∧
      Real.log 2 ≤
        cd * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
          badTailOffset theta Cblk qfb b)) * ((3 : ℝ) ^ (mu / 2) - 1) ∧
      2 * Real.log 4 ≤
        cd * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) -
          badTailOffset theta Cblk qfb b)) ∧
      (3 : ℝ) ^ (2 * mu *
          ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ))) ≤
        cd / 2 * Bconst ^ (2 * mu) ∧
      (N0 : ℝ) ≤ admissibleGenerationBound nstar qfb b theta mu cd Cblk + 1 ∧
      Bconst = normalizerWitness mu cd
        ((3 : ℝ) ^ (2 * mu *
          ((nstar : ℝ) + badTailOffset theta Cblk qfb b - (N0 : ℝ)))) := by
  set c1 : ℝ := rowSplitOffset theta Cblk with hc1
  set c2 : ℝ := badTailOffset theta Cblk qfb b with hc2
  set M : ℝ :=
    max (Real.log 2 / ((3 : ℝ) ^ (mu / 2) - 1)) (2 * Real.log 4) with hM
  set X : ℝ := admissibleGenerationBound nstar qfb b theta mu cd Cblk with hX
  have hXeq : X = max (max ((nstar : ℝ))
        ((nstar : ℝ) + ((qfb : ℝ) + (b : ℝ) + 1 + c1)))
      ((nstar : ℝ) + c2 + (M / cd - 1) / (2 * mu * Real.log 3)) := by
    rw [hX, admissibleGenerationBound, hc1, hc2, hM]
  set N0 : ℕ := ⌈X⌉₊ with hN0def
  have hXle : X ≤ (N0 : ℝ) := Nat.le_ceil X
  have hX0 : (0 : ℝ) ≤ X := by
    have hpos : (0 : ℝ) ≤ max ((nstar : ℝ))
        ((nstar : ℝ) + ((qfb : ℝ) + (b : ℝ) + 1 + c1)) :=
      le_trans (Nat.cast_nonneg nstar) (le_max_left _ _)
    rw [hXeq]
    exact le_trans hpos (le_max_left _ _)
  have hceil : (N0 : ℝ) ≤ X + 1 := by
    rw [hN0def]
    exact (Nat.ceil_lt_add_one hX0).le
  have hNstar : (nstar : ℝ) ≤ (N0 : ℝ) := by
    refine le_trans ?_ hXle
    rw [hXeq]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hNlow : (nstar : ℝ) + ((qfb : ℝ) + (b : ℝ) + 1 + c1) ≤ (N0 : ℝ) := by
    refine le_trans ?_ hXle
    rw [hXeq]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hNL : (nstar : ℝ) + c2 + (M / cd - 1) / (2 * mu * Real.log 3) ≤
      (N0 : ℝ) := by
    refine le_trans ?_ hXle
    rw [hXeq]
    exact le_max_right _ _
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hone : (3 : ℝ) ^ (0 : ℝ) < (3 : ℝ) ^ (mu / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith only [hmu])
  rw [Real.rpow_zero] at hone
  have hfac : (0 : ℝ) < (3 : ℝ) ^ (mu / 2) - 1 := by linarith only [hone]
  have hden : (0 : ℝ) < 2 * mu * Real.log 3 := by positivity
  have hlin : M / cd - 1 ≤
      (2 * mu * Real.log 3) * ((N0 : ℝ) - (nstar : ℝ) - c2) := by
    have hstep : (M / cd - 1) / (2 * mu * Real.log 3) ≤
        (N0 : ℝ) - (nstar : ℝ) - c2 := by linarith only [hNL]
    have hres := (div_le_iff₀ hden).1 hstep
    linarith only [hres]
  have hpow : M ≤ cd * (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) - c2)) := by
    have hmin : Real.log 3 * (2 * mu * ((N0 : ℝ) - (nstar : ℝ) - c2)) + 1 ≤
        (3 : ℝ) ^ (2 * mu * ((N0 : ℝ) - (nstar : ℝ) - c2)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      exact Real.add_one_le_exp _
    have hlin' : M / cd ≤
        Real.log 3 * (2 * mu * ((N0 : ℝ) - (nstar : ℝ) - c2)) + 1 := by
      linarith only [hlin]
    have hmul := mul_le_mul_of_nonneg_left (le_trans hlin' hmin) hcd.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hcd)] at hmul
  have hZpos : (0 : ℝ) <
      (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + c2 - (N0 : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨N0, normalizerWitness mu cd
      ((3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + c2 - (N0 : ℝ)))),
    by exact_mod_cast hNstar, one_le_normalizerWitness _ _ _, by
      linarith only [hNlow], ?_, ?_,
    le_mul_normalizerWitness hmu hcd hZpos, hceil, rfl⟩
  · have hMfac : Real.log 2 ≤ M * ((3 : ℝ) ^ (mu / 2) - 1) := by
      have hle : Real.log 2 / ((3 : ℝ) ^ (mu / 2) - 1) ≤ M := le_max_left _ _
      have hstep := mul_le_mul_of_nonneg_right hle hfac.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hfac)] at hstep
    exact le_trans hMfac (mul_le_mul_of_nonneg_right hpow hfac.le)
  · exact le_trans (le_max_right _ _) hpow

end

end Quenched
end HighContrast
end HCPolySupport

/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedGenerationTail
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# High-contrast homogenization: Provider.Quenched.RowDecayAESummability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Almost-everywhere summability from stopping-generation decay

The stopping-generation tail is uniform in the outer generation.  Along the
diagonal where the allowed stopping offset grows linearly, its probabilities
are super-geometrically summable.  Borel--Cantelli therefore makes the row
decay strong enough to sum every weighted tail almost everywhere.
-/

namespace HCPolySupport.HighContrast.Quenched

open Filter MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

private theorem ae_eventually_stoppingGeneration_le_quarter
    {P : Measure Omega} [IsProbabilityMeasure P]
    {nstar qfb b : ℕ} {R : ℕ → Omega → ℝ} {mu cd : ℝ}
    (hmu : 0 < mu) (hcd : 0 < cd)
    (hRtail : ∀ n q : ℕ, nstar ≤ n →
      P.real {ω | (3 : ℝ) ^ (n + q + b) < R n ω} ≤
        Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ))))) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop,
      (stoppingGeneration nstar qfb R (nstar + qfb + b + 1 + j) ω : ℝ) ≤
        (j : ℝ) / 4 +
          (((nstar + qfb + b + 1 : ℕ) : ℝ) - (nstar : ℝ)) := by
  let n0 : ℕ := nstar + qfb + b + 1
  let E : ℕ → Set Omega := fun j =>
    {ω | (j : ℝ) / 4 + ((n0 : ℝ) - (nstar : ℝ)) <
      (stoppingGeneration nstar qfb R (n0 + j) ω : ℝ)}
  have hoffset : (qfb : ℝ) + (b : ℝ) + 1 =
      (n0 : ℝ) - (nstar : ℝ) := by
    dsimp only [n0]
    push_cast
    ring_nf
  have hEbound : ∀ j : ℕ,
      P.real (E j) ≤
        Real.exp (-(cd * (3 : ℝ) ^ (mu / 2 * (j : ℝ)))) := by
    intro j
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / 4 := by positivity
    have hy : (qfb : ℝ) + (b : ℝ) + 1 ≤
        (j : ℝ) / 4 + ((n0 : ℝ) - (nstar : ℝ)) := by
      rw [hoffset]
      linarith only [hj0]
    have htail := measureReal_stoppingGeneration_gt_real_le
      (P := P) (nstar := nstar) (qfb := qfb) (b := b) (R := R)
      hmu hcd hRtail (n0 + j) hy
    refine htail.trans (le_of_eq ?_)
    congr 1
    congr 2
    rw [← hoffset]
    ring_nf
  have htailSummable : Summable fun j : ℕ =>
      Real.exp (-(cd * (3 : ℝ) ^ (mu / 2 * (j : ℝ)))) :=
    summable_exp_neg_triadic hcd (by linarith only [hmu])
  have hrealSummable : Summable fun j : ℕ => P.real (E j) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) hEbound htailSummable
  have hmeasureSummable : (∑' j : ℕ, P (E j)) ≠ ⊤ := by
    have heq : (fun j : ℕ => P (E j)) =
        fun j => ENNReal.ofReal (P.real (E j)) := by
      funext j
      exact (ENNReal.ofReal_toReal (measure_ne_top P (E j))).symm
    rw [heq]
    exact hrealSummable.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hmeasureSummable] with ω hω
  filter_upwards [hω] with j hj
  simpa only [n0, E, Set.mem_ofPred_eq, not_lt] using hj

omit [MeasurableSpace Omega] in
private theorem summable_shifted_row_of_stoppingGeneration_le_quarter
    {nstar qfb n0 : ℕ} {R B : ℕ → Omega → ℝ}
    {theta delta Cblk : ℝ} {omega : Omega}
    (hn0 : nstar ≤ n0) (htheta : 0 < theta)
    (hdelta : 0 < delta) (hCblk : 0 < Cblk)
    (hgood : ∀ᶠ j in atTop,
      (stoppingGeneration nstar qfb R (n0 + j) omega : ℝ) ≤
        (j : ℝ) / 4 + ((n0 : ℝ) - (nstar : ℝ)))
    (hdecay : ∀ (m : ℕ), nstar ≤ m →
      B m omega ≤ Cblk * delta *
        (3 : ℝ) ^ (-theta *
          ((m : ℝ) - (stoppingGeneration nstar qfb R m omega : ℝ) -
            (nstar : ℝ))))
    (hBnonneg : ∀ m, 0 ≤ B m omega) :
    Summable fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * ((n0 + j : ℕ) : ℝ)) * B (n0 + j) omega := by
  have hmajorant : Summable fun j : ℕ =>
      (Cblk * delta * (3 : ℝ) ^ (theta / 2 * (n0 : ℝ))) *
        ((3 : ℝ) ^ (-theta / 4)) ^ j := by
    have hq0 : 0 ≤ (3 : ℝ) ^ (-theta / 4) := by positivity
    have hq1 : (3 : ℝ) ^ (-theta / 4) < 1 := by
      rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
      exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2
        (by linarith only [htheta])
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine hmajorant.of_norm_bounded_eventually_nat ?_
  filter_upwards [hgood] with j hj
  have hdecayAt := hdecay (n0 + j) (le_trans hn0 (Nat.le_add_right n0 j))
  have hexponent :
      -theta * (((n0 + j : ℕ) : ℝ) -
        (stoppingGeneration nstar qfb R (n0 + j) omega : ℝ) -
        (nstar : ℝ)) ≤ -theta * (3 * (j : ℝ) / 4) := by
    have hgap : 3 * (j : ℝ) / 4 ≤ ((n0 + j : ℕ) : ℝ) -
        (stoppingGeneration nstar qfb R (n0 + j) omega : ℝ) -
        (nstar : ℝ) := by
      push_cast
      linarith only [hj]
    exact mul_le_mul_of_nonpos_left hgap (by linarith only [htheta])
  have hrpow : (3 : ℝ) ^ (-theta * (((n0 + j : ℕ) : ℝ) -
        (stoppingGeneration nstar qfb R (n0 + j) omega : ℝ) -
        (nstar : ℝ))) ≤
      (3 : ℝ) ^ (-theta * (3 * (j : ℝ) / 4)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hrow := hdecayAt.trans
    (mul_le_mul_of_nonneg_left hrpow (mul_nonneg hCblk.le hdelta.le))
  have hweighted :
      (3 : ℝ) ^ (theta / 2 * ((n0 + j : ℕ) : ℝ)) * B (n0 + j) omega ≤
        (3 : ℝ) ^ (theta / 2 * ((n0 + j : ℕ) : ℝ)) *
          (Cblk * delta * (3 : ℝ) ^ (-theta * (3 * (j : ℝ) / 4))) :=
    mul_le_mul_of_nonneg_left hrow (Real.rpow_nonneg (by norm_num) _)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hBnonneg _))]
  refine hweighted.trans_eq ?_
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-theta / 4)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hexpEq :
      theta / 2 * ((n0 + j : ℕ) : ℝ) - theta * (3 * (j : ℝ) / 4) =
        theta / 2 * (n0 : ℝ) + -theta / 4 * (j : ℝ) := by
    push_cast
    ring_nf
  calc
    (3 : ℝ) ^ (theta / 2 * ((n0 + j : ℕ) : ℝ)) *
          (Cblk * delta * (3 : ℝ) ^ (-theta * (3 * (j : ℝ) / 4))) =
        Cblk * delta * ((3 : ℝ) ^ (theta / 2 * ((n0 + j : ℕ) : ℝ)) *
          (3 : ℝ) ^ (-theta * (3 * (j : ℝ) / 4))) := by ring_nf
    _ = Cblk * delta * (3 : ℝ) ^
        (theta / 2 * ((n0 + j : ℕ) : ℝ) - theta * (3 * (j : ℝ) / 4)) := by
      rw [show theta / 2 * ((n0 + j : ℕ) : ℝ) - theta * (3 * (j : ℝ) / 4) =
        theta / 2 * ((n0 + j : ℕ) : ℝ) +
          (-theta * (3 * (j : ℝ) / 4)) by ring_nf]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    _ = Cblk * delta * (3 : ℝ) ^
        (theta / 2 * (n0 : ℝ) + -theta / 4 * (j : ℝ)) := by rw [hexpEq]
    _ = Cblk * delta * (3 : ℝ) ^ (theta / 2 * (n0 : ℝ)) *
        (3 : ℝ) ^ (-theta / 4 * (j : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring_nf

omit [MeasurableSpace Omega] in
private theorem summable_all_weighted_tails_of_shifted
    {B : ℕ → Omega → ℝ} {theta : ℝ} {n0 : ℕ} {omega : Omega}
    (hshifted : Summable fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * ((n0 + j : ℕ) : ℝ)) * B (n0 + j) omega) :
    ∀ k : ℕ, Summable fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (k + j) omega := by
  have habsolute : Summable fun m : ℕ =>
      (3 : ℝ) ^ (theta / 2 * (m : ℝ)) * B m omega :=
    (summable_nat_add_iff
      (f := fun m : ℕ => (3 : ℝ) ^ (theta / 2 * (m : ℝ)) * B m omega)
      n0).1 (by simpa only [Nat.add_comm] using hshifted)
  intro k
  have htail := (summable_nat_add_iff
    (f := fun m : ℕ => (3 : ℝ) ^ (theta / 2 * (m : ℝ)) * B m omega)
    k).2 habsolute
  have hfactor : (fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (k + j) omega) =
      fun j => (3 : ℝ) ^ (-(theta / 2 * (k : ℝ))) *
        ((3 : ℝ) ^ (theta / 2 * ((j + k : ℕ) : ℝ)) * B (j + k) omega) := by
    funext j
    have hp : (3 : ℝ) ^ (theta / 2 * (j : ℝ)) =
        (3 : ℝ) ^ (-(theta / 2 * (k : ℝ))) *
          (3 : ℝ) ^ (theta / 2 * ((j + k : ℕ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring_nf
    rw [Nat.add_comm k j, hp]
    ring_nf
  rw [hfactor]
  exact htail.mul_left _

/-- Almost-everywhere row decay against a stopping family supplies the
almost-everywhere weighted summability required by the coupled engine. -/
theorem ae_summable_weighted_row_of_stoppingGeneration
    {P : Measure Omega} [IsProbabilityMeasure P]
    {nstar qfb b : ℕ} {R B : ℕ → Omega → ℝ}
    {theta mu cd delta Cblk : ℝ}
    (htheta : 0 < theta) (hmu : 0 < mu) (hcd : 0 < cd)
    (hdelta : 0 < delta) (hCblk : 0 < Cblk)
    (hRtail : ∀ n q : ℕ, nstar ≤ n →
      P.real {ω | (3 : ℝ) ^ (n + q + b) < R n ω} ≤
        Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))))
    (hBdecay : ∀ᵐ ω ∂P, ∀ (m : ℕ), nstar ≤ m →
      B m ω ≤ Cblk * delta *
        (3 : ℝ) ^ (-theta *
          ((m : ℝ) - (stoppingGeneration nstar qfb R m ω : ℝ) -
            (nstar : ℝ))))
    (hBnonneg : ∀ m ω, 0 ≤ B m ω) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Summable fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (k + j) ω := by
  let n0 : ℕ := nstar + qfb + b + 1
  have hn0 : nstar ≤ n0 := by
    dsimp only [n0]
    omega
  have hgoodAE := ae_eventually_stoppingGeneration_le_quarter
    (P := P) (nstar := nstar) (qfb := qfb) (b := b) (R := R)
    hmu hcd hRtail
  filter_upwards [hgoodAE, hBdecay]
    with ω hgood hdecay
  have hshifted : Summable fun j : ℕ =>
      (3 : ℝ) ^ (theta / 2 * ((n0 + j : ℕ) : ℝ)) * B (n0 + j) ω :=
    summable_shifted_row_of_stoppingGeneration_le_quarter hn0 htheta hdelta hCblk
      (by simpa only [n0] using hgood) hdecay (fun m => hBnonneg m ω)
  exact summable_all_weighted_tails_of_shifted hshifted

end

end HCPolySupport.HighContrast.Quenched

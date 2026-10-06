/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedRowSeries

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedGenerationTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One generation of the quenched bad-event estimate

The stopping radii of the endgame carry a Gaussian gauge at every shifted
offset: the shifted tail of the quenched radius, read with the Gaussian
concentration gauge supplied by unit range of dependence.  This file passes that
estimate to real thresholds, exactly as the stopping construction of
`ss.random.dirichlet` does after the tail of its stopping index, and sums the
resulting
super-geometric family over the generations of the weighted row series.  The
outcome is a single stretched-exponential estimate for one bad event.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The deterministic offset of the bad-event estimate: the split offset of the
weighted row series together with the shift of the stopping-radius gauge. -/
@[expose]
def badTailOffset (theta Cblk : ℝ) (qfb b : ℕ) : ℝ :=
  rowSplitOffset theta Cblk + 1 + (qfb : ℝ) + (b : ℝ)

/-- The stopping estimate holds at every real threshold, not only at the triadic
ones. -/
theorem measureReal_stoppingGeneration_gt_real_le
    {P : Measure Ω} [IsProbabilityMeasure P] {nstar qfb b : ℕ} {R : ℕ → Ω → ℝ}
    {mu cd : ℝ} (hmu : 0 < mu) (hcd : 0 < cd)
    (hRtail : ∀ n q : ℕ, nstar ≤ n →
      P.real {ω | (3 : ℝ) ^ (n + q + b) < R n ω} ≤
        Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))))
    (m : ℕ) {y : ℝ} (hy : (qfb : ℝ) + (b : ℝ) + 1 ≤ y) :
    P.real {ω | y < (stoppingGeneration nstar qfb R m ω : ℝ)} ≤
      Real.exp (-(cd * (3 : ℝ) ^
        (2 * mu * (y - 1 - (qfb : ℝ) - (b : ℝ))))) := by
  have hq0 : (0 : ℝ) ≤ (qfb : ℝ) := Nat.cast_nonneg qfb
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hy0 : (0 : ℝ) ≤ y := by linarith only [hy, hq0, hb0]
  have hfloor : qfb + b + 1 ≤ ⌊y⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith only [hy]
  set q : ℕ := ⌊y⌋₊ - (qfb + b) with hqdef
  have hqsum : q + (qfb + b) = ⌊y⌋₊ := by omega
  have hsub : {ω | y < (stoppingGeneration nstar qfb R m ω : ℝ)} ⊆
      {ω | q + (qfb + b) < stoppingGeneration nstar qfb R m ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hqsum]
    exact (Nat.floor_lt hy0).2 hω
  have hbnd := measureReal_stoppingGeneration_gt_le
    (P := P) (nstar := nstar) (qfb := qfb) (b := b) (R := R)
    (bnd := fun q => Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))))
    (fun _ => (Real.exp_pos _).le) hRtail m q
  refine (measureReal_mono hsub).trans (hbnd.trans ?_)
  have hqcast : (q : ℝ) + ((qfb : ℝ) + (b : ℝ)) = (⌊y⌋₊ : ℝ) := by
    have hcast : ((q + (qfb + b) : ℕ) : ℝ) = ((⌊y⌋₊ : ℕ) : ℝ) := by rw [hqsum]
    push_cast at hcast
    linarith only [hcast]
  have hfl : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hqreal : y - 1 - (qfb : ℝ) - (b : ℝ) ≤ (q : ℝ) := by
    linarith only [hqcast, hfl]
  have hexpLe : 2 * mu * (y - 1 - (qfb : ℝ) - (b : ℝ)) ≤ 2 * mu * (q : ℝ) :=
    mul_le_mul_of_nonneg_left hqreal (by linarith only [hmu])
  have hrpowLe : (3 : ℝ) ^ (2 * mu * (y - 1 - (qfb : ℝ) - (b : ℝ))) ≤
      (3 : ℝ) ^ (2 * mu * (q : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpLe
  exact Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_left hrpowLe hcd.le))

/-- The bad event of one generation of the weighted row series carries a
stretched-exponential estimate. -/
theorem measureReal_rowBadEvent_le
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
    {n : ℕ} (hn : nstar ≤ n)
    (hlow : (qfb : ℝ) + (b : ℝ) + 1 + rowSplitOffset theta Cblk ≤
      (n : ℝ) - (nstar : ℝ))
    (hgain : Real.log 2 ≤
      cd * (3 : ℝ) ^ (2 * mu * ((n : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)) * ((3 : ℝ) ^ (mu / 2) - 1)) :
    P.real (rowBadEvent delta F n) ≤
      2 * Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * ((n : ℝ) - (nstar : ℝ) -
        badTailOffset theta Cblk qfb b)))) := by
  set c1 : ℝ := rowSplitOffset theta Cblk with hc1
  set c2 : ℝ := badTailOffset theta Cblk qfb b with hc2
  have hc2eq : c2 = c1 + 1 + (qfb : ℝ) + (b : ℝ) := by
    rw [hc2, hc1, badTailOffset]
  set A : ℝ := cd * (3 : ℝ) ^ (2 * mu * ((n : ℝ) - (nstar : ℝ) - c2)) with hA
  have hApos : 0 < A := by
    rw [hA]
    have : (0 : ℝ) < (3 : ℝ) ^ (2 * mu * ((n : ℝ) - (nstar : ℝ) - c2)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact mul_pos hcd this
  set E : ℕ → Set Ω := fun j =>
    {ω | (j : ℝ) / 4 + ((n : ℝ) - (nstar : ℝ)) - c1 <
      (stoppingGeneration nstar qfb R (n + j) ω : ℝ)} with hE
  have hEbound : ∀ j : ℕ,
      P.real (E j) ≤ Real.exp (-(A * (3 : ℝ) ^ (mu / 2 * (j : ℝ)))) := by
    intro j
    have hjq : (0 : ℝ) ≤ (j : ℝ) / 4 := by
      have := Nat.cast_nonneg (α := ℝ) j
      linarith only [this]
    have hy : (qfb : ℝ) + (b : ℝ) + 1 ≤
        (j : ℝ) / 4 + ((n : ℝ) - (nstar : ℝ)) - c1 := by
      linarith only [hlow, hjq]
    have hstep := measureReal_stoppingGeneration_gt_real_le
      (P := P) (nstar := nstar) (qfb := qfb) (b := b) (R := R)
      hmu hcd hRtail (n + j) hy
    refine le_trans hstep (le_of_eq ?_)
    congr 1
    have hexp :
        2 * mu * (((j : ℝ) / 4 + ((n : ℝ) - (nstar : ℝ)) - c1) - 1 -
            (qfb : ℝ) - (b : ℝ)) =
          2 * mu * ((n : ℝ) - (nstar : ℝ) - c2) + mu / 2 * (j : ℝ) := by
      rw [hc2eq]
      ring
    rw [hexp, Real.rpow_add (by norm_num), hA]
    ring
  have hnu : (0 : ℝ) < mu / 2 := by linarith only [hmu]
  have hsummableExp :
      Summable fun j : ℕ => Real.exp (-(A * (3 : ℝ) ^ (mu / 2 * (j : ℝ)))) :=
    summable_exp_neg_triadic hApos hnu
  have hsummableE : Summable fun j : ℕ => P.real (E j) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) hEbound hsummableExp
  have hunion : P.real (⋃ j : ℕ, E j) ≤ ∑' j : ℕ, P.real (E j) :=
    Book.Ch05.Section57.measureReal_iUnion_nat_le_tsum hsummableE
  have htsum : ∑' j : ℕ, P.real (E j) ≤ 2 * Real.exp (-A) :=
    le_trans (hsummableE.tsum_le_tsum hEbound hsummableExp)
      (tsum_exp_neg_triadic_le_two_mul hApos.le hnu.le hgain)
  have hae : (rowBadEvent delta F n) ≤ᵐ[P] (⋃ j : ℕ, E j) := by
    filter_upwards [hFsum, hBdecay] with ω hω hBω hmem
    have hBpoint : ∀ (m : ℕ), nstar ≤ m →
        B m ω ≤ Cblk * delta *
          (3 : ℝ) ^ (-theta *
            ((m : ℝ) - (stoppingGeneration nstar qfb R m ω : ℝ) -
              (nstar : ℝ))) :=
      fun m hm => hBω m hm
    obtain ⟨j, hj⟩ := exists_lt_stoppingGeneration_of_rowBadEvent
      (R := R) (B := B) (F := F) htheta hdelta hCblk hn hBpoint (hω n) hmem
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    simp only [hE, Set.mem_ofPred_eq]
    exact hj
  have hmono : P.real (rowBadEvent delta F n) ≤ P.real (⋃ j : ℕ, E j) :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hae)
  exact hmono.trans (hunion.trans htsum)

end

end Quenched
end HighContrast
end HCPolySupport

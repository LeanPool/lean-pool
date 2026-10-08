/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SuperGeometricTail

/-!
# High-contrast homogenization: Provider.Quenched.QuenchedRowSeries

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weighted row series and its bad events

The endgame weights the block rows of the successive generations by a growing
triadic factor and stops at the first generation whose weighted tail series stays
below a fixed threshold (`e.random.adapted.sum`,
`e.random.final.scale`).  This file fixes the resulting bad
events, proves that a bad event forces one later generation map to be large, and
turns the resulting union bound into a single stretched-exponential estimate for
one generation.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The bad events of the weighted row series -/

/-- The bad event at a generation: the weighted tail series of the block rows
reaches the threshold. -/
@[expose]
def rowBadEvent (delta : ℝ) (F : ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | delta ≤ F n ω}

/-- The bad events are measurable as soon as the tail series is. -/
theorem measurableSet_rowBadEvent {F : ℕ → Ω → ℝ}
    (hF : ∀ n, Measurable (F n)) (delta : ℝ) (n : ℕ) :
    MeasurableSet (rowBadEvent delta F n) :=
  measurableSet_le measurable_const (hF n)

/-! ## The deterministic split offset -/

/-- The deterministic offset that absorbs the summable weights and the row
constant when the weighted series is split across generations. -/
@[expose]
def rowSplitOffset (theta Cblk : ℝ) : ℝ :=
  -Real.logb 3 ((1 - (3 : ℝ) ^ (-theta / 4)) / (2 * Cblk)) / theta

/-- The triadic weight at the base of the split offset is below one. -/
theorem rpow_neg_div_lt_one {theta : ℝ} (htheta : 0 < theta) :
    (3 : ℝ) ^ (-theta / 4) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [htheta])

/-- The split offset is the exact triadic exponent of the absorbed constant. -/
theorem rpow_neg_mul_rowSplitOffset {theta Cblk : ℝ} (htheta : 0 < theta)
    (hCblk : 0 < Cblk) :
    (3 : ℝ) ^ (-theta * rowSplitOffset theta Cblk) =
      (1 - (3 : ℝ) ^ (-theta / 4)) / (2 * Cblk) := by
  have hlt := rpow_neg_div_lt_one htheta
  have hpos : 0 < (1 - (3 : ℝ) ^ (-theta / 4)) / (2 * Cblk) := by
    apply div_pos
    · linarith only [hlt]
    · linarith only [hCblk]
  have hexp : -theta * rowSplitOffset theta Cblk =
      Real.logb 3 ((1 - (3 : ℝ) ^ (-theta / 4)) / (2 * Cblk)) := by
    rw [rowSplitOffset]
    field_simp
  rw [hexp]
  exact Real.rpow_logb (by norm_num) (by norm_num) hpos

/-! ## A bad row series forces a large generation map -/

omit [MeasurableSpace Ω] in
/-- On the summability event a bad weighted row series forces the generation map
of one later generation to exceed the split threshold. -/
theorem exists_lt_stoppingGeneration_of_rowBadEvent
    {nstar qfb : ℕ} {R B F : ℕ → Ω → ℝ} {theta delta Cblk : ℝ}
    (htheta : 0 < theta) (hdelta : 0 < delta) (hCblk : 0 < Cblk)
    {n : ℕ} (hn : nstar ≤ n) {ω : Ω}
    (hBdecay : ∀ (m : ℕ), nstar ≤ m →
      B m ω ≤ Cblk * delta *
        (3 : ℝ) ^ (-theta *
          ((m : ℝ) - (stoppingGeneration nstar qfb R m ω : ℝ) - (nstar : ℝ))))
    (hsum : HasSum
      (fun j : ℕ => (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (n + j) ω) (F n ω))
    (hbad : ω ∈ rowBadEvent delta F n) :
    ∃ j : ℕ,
      (j : ℝ) / 4 + ((n : ℝ) - (nstar : ℝ)) - rowSplitOffset theta Cblk <
        (stoppingGeneration nstar qfb R (n + j) ω : ℝ) := by
  by_contra hcon
  push Not at hcon
  set rr : ℝ := (3 : ℝ) ^ (-theta / 4) with hrr
  have hrrpos : 0 < rr := Real.rpow_pos_of_pos (by norm_num) _
  have hrrlt : rr < 1 := rpow_neg_div_lt_one htheta
  have habsorb := rpow_neg_mul_rowSplitOffset (Cblk := Cblk) htheta hCblk
  have hterm : ∀ j : ℕ,
      (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (n + j) ω ≤
        delta * (1 - rr) / 2 * rr ^ j := by
    intro j
    have hNle := hcon j
    have hcast : ((n + j : ℕ) : ℝ) = (n : ℝ) + (j : ℝ) := by push_cast; ring
    have hmul :
        theta * (stoppingGeneration nstar qfb R (n + j) ω : ℝ) ≤
          theta * ((j : ℝ) / 4 + ((n : ℝ) - (nstar : ℝ)) -
            rowSplitOffset theta Cblk) :=
      mul_le_mul_of_nonneg_left hNle htheta.le
    have hexpLe :
        -theta * (((n + j : ℕ) : ℝ) -
            (stoppingGeneration nstar qfb R (n + j) ω : ℝ) - (nstar : ℝ)) ≤
          -theta * rowSplitOffset theta Cblk + -(3 * theta / 4) * (j : ℝ) := by
      rw [hcast]
      linarith only [hmul]
    have hrpowLe :
        (3 : ℝ) ^ (-theta * (((n + j : ℕ) : ℝ) -
            (stoppingGeneration nstar qfb R (n + j) ω : ℝ) - (nstar : ℝ))) ≤
          (3 : ℝ) ^ (-theta * rowSplitOffset theta Cblk +
            -(3 * theta / 4) * (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpLe
    have hB := hBdecay (n + j) (le_trans hn (Nat.le_add_right n j))
    have hCd : 0 ≤ Cblk * delta := le_of_lt (mul_pos hCblk hdelta)
    have hweight : (0 : ℝ) ≤ (3 : ℝ) ^ (theta / 2 * (j : ℝ)) :=
      le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    have hstep1 :
        (3 : ℝ) ^ (theta / 2 * (j : ℝ)) * B (n + j) ω ≤
          (3 : ℝ) ^ (theta / 2 * (j : ℝ)) *
            (Cblk * delta *
              (3 : ℝ) ^ (-theta * rowSplitOffset theta Cblk +
                -(3 * theta / 4) * (j : ℝ))) := by
      refine mul_le_mul_of_nonneg_left (le_trans hB ?_) hweight
      exact mul_le_mul_of_nonneg_left hrpowLe hCd
    have hsplit :
        (3 : ℝ) ^ (-theta * rowSplitOffset theta Cblk +
            -(3 * theta / 4) * (j : ℝ)) =
          (1 - rr) / (2 * Cblk) * (3 : ℝ) ^ (-(3 * theta / 4) * (j : ℝ)) := by
      rw [Real.rpow_add (by norm_num), habsorb]
    have hcombine :
        (3 : ℝ) ^ (theta / 2 * (j : ℝ)) *
            (3 : ℝ) ^ (-(3 * theta / 4) * (j : ℝ)) = rr ^ j := by
      rw [← Real.rpow_add (by norm_num)]
      have hsum2 : theta / 2 * (j : ℝ) + -(3 * theta / 4) * (j : ℝ) =
          -theta / 4 * (j : ℝ) := by ring
      rw [hsum2, hrr, ← Real.rpow_natCast ((3 : ℝ) ^ (-theta / 4)) j,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hfinal :
        (3 : ℝ) ^ (theta / 2 * (j : ℝ)) *
            (Cblk * delta *
              (3 : ℝ) ^ (-theta * rowSplitOffset theta Cblk +
                -(3 * theta / 4) * (j : ℝ))) =
          delta * (1 - rr) / 2 * rr ^ j := by
      rw [hsplit, ← hcombine]
      field_simp
    exact hstep1.trans_eq hfinal
  have hsummable_bound : Summable fun j : ℕ => delta * (1 - rr) / 2 * rr ^ j :=
    (summable_geometric_of_lt_one hrrpos.le hrrlt).mul_left _
  have hne : (1 : ℝ) - rr ≠ 0 := ne_of_gt (by linarith only [hrrlt])
  have htsum : ∑' j : ℕ, delta * (1 - rr) / 2 * rr ^ j = delta / 2 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hrrpos.le hrrlt]
    field_simp
  have hle : F n ω ≤ delta / 2 := by
    rw [← hsum.tsum_eq, ← htsum]
    exact hsum.summable.tsum_le_tsum hterm hsummable_bound
  have hbad' : delta ≤ F n ω := hbad
  linarith only [hle, hbad', hdelta]

end

end Quenched
end HighContrast
end HCPolySupport

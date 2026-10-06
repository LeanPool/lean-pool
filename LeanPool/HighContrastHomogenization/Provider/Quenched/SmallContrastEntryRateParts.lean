/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionAdapters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHrecInstance

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryRateParts

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The three source-decay parts of the entry estimate

the corresponding argument named three missing sub-estimates behind `hentry`; this file supplies
them, each with its constant named, and repairs a rate leak found on the way.

**The leak.**  The slot-source split bounds the weighted slot source by
`(H_w+1)·(c₁+c₂+c₃)·3^{-J/2}`.  The factor `H_w + 1` is an artefact of the
coarse shallow exponent `e ≥ 1/2` used there: the shallow legs are then bounded
by `3^{-j/2}·3^{-(J-j)/2} = 3^{-J/2}`, a *constant* in `j`, and summing `J+1` of
them costs the window height.  In the construction the shallow exponent is `e = d/2`,
which for `d ≥ 2` is at least `1`; then the shallow legs are bounded by
`3^{-J/2}·3^{-(J-j)/2}`, which is *geometric* in the lag, and the sum is
`halfGeom·3^{-J/2}` with no window factor at all.

This matters because the margin is exactly nil: the deep-leg source decays at
rate `1/2` in the lag `J`, `J ≈ n/4` per generation, so the achievable rate is
`1/8` per generation, and `recursionAlpha 0 = 1/8`.  Any extra polynomial factor
destroys the rate at `g = 0`.  `slot_source_sum_split_sharp` removes it.

**The three parts.**

* (a) `slotVsumSharp_le` — the variance leg, `≤ C_v·3^{-J/2}`;
* (b) the profile bad-majorant moment bound — the bad-event leg,
  `≤ C_b·3^{-Δ/2}` in the absolute-generation gap `Δ`;
* (c) the window-tail bound, `3^{-contrastAlpha g·H_w}`, restated at
  a common rate.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The half-step ratio -/

/-- The one-step ratio of the linear weight, `3^{-1/2}`. -/
@[expose]
def halfRatio : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ))

theorem halfRatio_pos : 0 < halfRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem halfRatio_lt_one : halfRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem halfGeom_eq_inv : halfGeom = (1 - halfRatio)⁻¹ := by
  rw [halfGeom, halfRatio]

theorem halfGeom_one_le : (1 : ℝ) ≤ halfGeom := by
  rw [halfGeom_eq_inv]
  have h0 : 0 < 1 - halfRatio := by linarith only [halfRatio_lt_one]
  rw [le_inv_comm₀ (by norm_num) h0]
  simp only [inv_one]
  linarith only [halfRatio_pos]

theorem linWeight_eq_pow (j : ℕ) : linWeight j = halfRatio ^ j := by
  rw [linWeight, halfRatio]
  exact rpow_weight_eq_pow (mu := (1 / 2 : ℝ)) j

theorem halfRatio_geom_sum_le (m : ℕ) :
    ∑ k ∈ Finset.range m, halfRatio ^ k ≤ halfGeom := by
  rw [halfGeom_eq_inv]
  exact geom_sum_le_inv_one_sub halfRatio_pos.le halfRatio_lt_one m

theorem halfRatio_sq : halfRatio ^ 2 = (3 : ℝ) ^ (-(1 : ℝ)) := by
  rw [halfRatio, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The unit-rate weight is the square of the half-rate weight. -/
theorem rpow_neg_one_mul_eq_pow (m : ℕ) :
    (3 : ℝ) ^ (-(1 : ℝ) * (m : ℝ)) = halfRatio ^ (2 * m) := by
  rw [rpow_weight_eq_pow (mu := (1 : ℝ)) m, pow_mul, halfRatio_sq]

/-- A shallow leg at exponent at least one is dominated by the unit-rate leg. -/
theorem rpow_neg_mul_le_pow {e : ℝ} (he : 1 ≤ e) (m : ℕ) :
    (3 : ℝ) ^ (-e * (m : ℝ)) ≤ halfRatio ^ (2 * m) := by
  rw [← rpow_neg_one_mul_eq_pow]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith only [he, hm]

/-! ## The sharp slot-source summation -/

/-- **The sharp slot-source summation.**  With the shallow exponent at least
one — which is `e = d/2` at `d ≥ 2` — the weighted source sum is geometric in
the lag, with no factor of the window height. -/
theorem slot_source_sum_split_sharp {Hw J : ℕ} {vs : ℕ → ℝ} {c1 c2 c3 e : ℝ}
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (he : 1 ≤ e)
    (hshallow : ∀ j ∈ Finset.range (Hw + 1), j ≤ J →
      vs j ≤ c1 * (3 : ℝ) ^ (-e * ((J - j : ℕ) : ℝ)) +
        c2 * (3 : ℝ) ^ (-(1 : ℝ) * ((J - j : ℕ) : ℝ)))
    (hdeep : ∀ j ∈ Finset.range (Hw + 1), J ≤ j → vs j ≤ c3) :
    ∑ j ∈ Finset.range (Hw + 1), linWeight j * vs j ≤
      halfGeom * (c1 + c2 + c3) * halfRatio ^ J := by
  classical
  have hr0 : (0 : ℝ) ≤ halfRatio := halfRatio_pos.le
  have hrJ : (0 : ℝ) ≤ halfRatio ^ J := pow_nonneg hr0 J
  have hgeom0 : (0 : ℝ) ≤ halfGeom := le_trans zero_le_one halfGeom_one_le
  -- the shallow half
  have hsh : ∑ j ∈ (Finset.range (Hw + 1)).filter (fun j => j ≤ J),
      linWeight j * vs j ≤ (c1 + c2) * halfGeom * halfRatio ^ J := by
    have hterm : ∀ j ∈ (Finset.range (Hw + 1)).filter (fun j => j ≤ J),
        linWeight j * vs j ≤
          (c1 + c2) * (halfRatio ^ J * halfRatio ^ (J - j)) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjr, hjJ⟩ := hj
      have hb := hshallow j hjr hjJ
      have h1 : (3 : ℝ) ^ (-e * ((J - j : ℕ) : ℝ)) ≤
          halfRatio ^ (2 * (J - j)) := rpow_neg_mul_le_pow he _
      have h2 : (3 : ℝ) ^ (-(1 : ℝ) * ((J - j : ℕ) : ℝ)) =
          halfRatio ^ (2 * (J - j)) := rpow_neg_one_mul_eq_pow _
      have hvs : vs j ≤ (c1 + c2) * halfRatio ^ (2 * (J - j)) := by
        rw [h2] at hb
        nlinarith only [hb, h1, hc1, hc2, pow_nonneg hr0 (2 * (J - j))]
      have hidx : j + 2 * (J - j) = J + (J - j) := by omega
      have hp : halfRatio ^ j * halfRatio ^ (2 * (J - j)) =
          halfRatio ^ J * halfRatio ^ (J - j) := by
        rw [← pow_add, ← pow_add, hidx]
      have hlw : linWeight j * ((c1 + c2) * halfRatio ^ (2 * (J - j))) =
          (c1 + c2) * (halfRatio ^ J * halfRatio ^ (J - j)) := by
        rw [linWeight_eq_pow]
        calc halfRatio ^ j * ((c1 + c2) * halfRatio ^ (2 * (J - j)))
            = (c1 + c2) * (halfRatio ^ j * halfRatio ^ (2 * (J - j))) := by ring
          _ = (c1 + c2) * (halfRatio ^ J * halfRatio ^ (J - j)) := by rw [hp]
      calc linWeight j * vs j
          ≤ linWeight j * ((c1 + c2) * halfRatio ^ (2 * (J - j))) := by
            rw [linWeight_eq_pow]
            exact mul_le_mul_of_nonneg_left hvs (pow_nonneg hr0 j)
        _ = (c1 + c2) * (halfRatio ^ J * halfRatio ^ (J - j)) := hlw
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsub : (Finset.range (Hw + 1)).filter (fun j => j ≤ J) ⊆
        Finset.range (J + 1) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      exact Finset.mem_range.mpr (by omega)
    have hnn : ∀ j ∈ Finset.range (J + 1),
        j ∉ (Finset.range (Hw + 1)).filter (fun j => j ≤ J) →
        (0 : ℝ) ≤ (c1 + c2) * (halfRatio ^ J * halfRatio ^ (J - j)) := by
      intro j _ _
      exact mul_nonneg (by linarith only [hc1, hc2])
        (mul_nonneg hrJ (pow_nonneg hr0 _))
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
    rw [← Finset.mul_sum]
    have hrefl : ∑ j ∈ Finset.range (J + 1), halfRatio ^ J * halfRatio ^ (J - j) =
        halfRatio ^ J * ∑ k ∈ Finset.range (J + 1), halfRatio ^ k := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_reflect (fun k => halfRatio ^ k) (J + 1)
    rw [hrefl]
    have hgs := halfRatio_geom_sum_le (J + 1)
    have hmul : halfRatio ^ J * ∑ k ∈ Finset.range (J + 1), halfRatio ^ k ≤
        halfRatio ^ J * halfGeom := mul_le_mul_of_nonneg_left hgs hrJ
    nlinarith only [hmul, hc1, hc2, hrJ, hgeom0]
  -- the deep half
  have hdp : ∑ j ∈ (Finset.range (Hw + 1)).filter (fun j => ¬ j ≤ J),
      linWeight j * vs j ≤ c3 * halfGeom * halfRatio ^ J := by
    have hset : (Finset.range (Hw + 1)).filter (fun j => ¬ j ≤ J) =
        Finset.Ico (J + 1) (Hw + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hset]
    have hterm : ∀ j ∈ Finset.Ico (J + 1) (Hw + 1),
        linWeight j * vs j ≤ c3 * (halfRatio ^ J * halfRatio ^ (j - J)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hjr : j ∈ Finset.range (Hw + 1) := Finset.mem_range.mpr hj.2
      have hb := hdeep j hjr (by omega)
      have hidx : j = J + (j - J) := by omega
      calc linWeight j * vs j ≤ linWeight j * c3 := by
            rw [linWeight_eq_pow]
            exact mul_le_mul_of_nonneg_left hb (pow_nonneg hr0 j)
        _ = c3 * (halfRatio ^ J * halfRatio ^ (j - J)) := by
            rw [linWeight_eq_pow]
            nth_rewrite 1 [hidx]
            rw [pow_add]
            ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
    have hidx : ∀ i ∈ Finset.range (Hw + 1 - (J + 1)),
        halfRatio ^ J * halfRatio ^ (J + 1 + i - J) ≤
          halfRatio ^ J * halfRatio ^ i := by
      intro i _
      have heq : J + 1 + i - J = 1 + i := by omega
      rw [heq]
      refine mul_le_mul_of_nonneg_left ?_ hrJ
      exact pow_le_pow_of_le_one hr0 halfRatio_lt_one.le (by omega)
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hidx) hc3) ?_
    rw [← Finset.mul_sum]
    have hgs := halfRatio_geom_sum_le (Hw + 1 - (J + 1))
    have hmul : halfRatio ^ J * ∑ k ∈ Finset.range (Hw + 1 - (J + 1)),
        halfRatio ^ k ≤ halfRatio ^ J * halfGeom :=
      mul_le_mul_of_nonneg_left hgs hrJ
    nlinarith only [hmul, hc3, hrJ, hgeom0]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Hw + 1))
    (fun j => j ≤ J)]
  nlinarith only [hsh, hdp, hrJ, hgeom0, hc1, hc2, hc3]

/-! ## Part (a): the variance leg -/

/-- The shallow exponent `d/2` is at least one at `d ≥ 2`. -/
theorem one_le_half_dim {d : ℕ} (hd : 2 ≤ d) : (1 : ℝ) ≤ (d : ℝ) / 2 := by
  have h : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith only [h]

/-- **The sharp summed source of the slot family.**  Identical to
`slotSourceSeq_sum_le_sharp` except that the window-height factor is gone. -/
theorem slotSourceSeq_sum_le_sharp {d : ℕ} (hd : 2 ≤ d) {Csub Msc delta : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta) (Hw J : ℕ) :
    ∑ j ∈ Finset.range (Hw + 1),
        linWeight j * slotSourceSeq d Csub Msc delta J j ≤
      halfGeom *
        (Real.sqrt (2 * d) * 18 * Csub * Msc + Real.sqrt (2 * d) * 288 +
          deepSlotConstant d Csub Msc delta) * halfRatio ^ J := by
  have hc1 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 18 * Csub * Msc := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  have hc2 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 288 := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  have hc3 : (0 : ℝ) ≤ deepSlotConstant d Csub Msc delta := by
    rw [deepSlotConstant]
    exact add_nonneg (slotSourceValue_nonneg d hCsub hMsc 0)
      (mul_nonneg (slotBaseCoefficient_nonneg d) hdelta)
  refine slot_source_sum_split_sharp hc1 hc2 hc3 (one_le_half_dim hd) ?_ ?_
  · intro j _ hjJ
    rw [slotSourceSeq, ite_eq_left hjJ, slotSourceValue_eq]
  · intro j _ hJj
    rcases eq_or_lt_of_le hJj with heq | hlt
    · rw [slotSourceSeq, ite_eq_left (le_of_eq heq.symm)]
      have hzero : J - j = 0 := by omega
      rw [hzero, deepSlotConstant]
      have h0 : (0 : ℝ) ≤ slotBaseCoefficient d * delta :=
        mul_nonneg (slotBaseCoefficient_nonneg d) hdelta
      linarith only [h0]
    · rw [slotSourceSeq, ite_eq_right (by omega)]

/-- **The sharp summed source constant** — the window-height-free replacement
for `slotVsumSharp`. -/
@[expose]
def slotVsumSharp (d : ℕ) (Csub Msc delta : ℝ) (J : ℕ) : ℝ :=
  halfGeom *
      (Real.sqrt (2 * d) * 18 * Csub * Msc + Real.sqrt (2 * d) * 288 +
        deepSlotConstant d Csub Msc delta) * halfRatio ^ J +
    halfGeom * slotSourceSeq d Csub Msc delta J 0

/-- **The `hVsum` hypothesis at the sharp constant.**  Drop-in replacement for
`hVsum_of_family_sharp`, with the same base coefficient `slotCVsum d`. -/
theorem hVsum_of_family_sharp {d : ℕ} (hd : 2 ≤ d) {Csub Msc delta Fjb : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta)
    (hFjb : 0 ≤ Fjb) (Hw J : ℕ) :
    ∑ j ∈ Finset.range (Hw + 1),
        linWeight j * (slotFamilyValue d Csub Msc delta Fjb J j +
          slotFamilyValue d Csub Msc delta Fjb J 0) ≤
      slotVsumSharp d Csub Msc delta J + slotCVsum d * Fjb := by
  have hbase : 0 ≤ slotBaseCoefficient d := slotBaseCoefficient_nonneg d
  have hv0 : 0 ≤ slotSourceSeq d Csub Msc delta J 0 :=
    slotSourceSeq_nonneg d hCsub hMsc hdelta J 0
  have hsum := slotSourceSeq_sum_le_sharp hd hCsub hMsc hdelta Hw J
  have hres := slot_sum_with_base (Hw := Hw)
    (V := fun j => slotFamilyValue d Csub Msc delta Fjb J j)
    (vs := fun j => slotSourceSeq d Csub Msc delta J j)
    (cV := slotBaseCoefficient d) (Fjb := Fjb)
    (V0 := slotFamilyValue d Csub Msc delta Fjb J 0)
    (v0src := slotSourceSeq d Csub Msc delta J 0)
    (cv0 := slotBaseCoefficient d)
    (vsrcSum := halfGeom *
      (Real.sqrt (2 * d) * 18 * Csub * Msc + Real.sqrt (2 * d) * 288 +
        deepSlotConstant d Csub Msc delta) * halfRatio ^ J)
    hbase hFjb (fun j _ => le_of_eq rfl) (le_of_eq rfl) hv0 hbase hsum
  rw [slotVsumSharp, slotCVsum]
  linarith only [hres]

/-- The variance leg's source constant. -/
@[expose]
def vsumSourceConstant (d : ℕ) (Csub Msc delta : ℝ) : ℝ :=
  halfGeom *
    (2 * (Real.sqrt (2 * d) * 18 * Csub * Msc) +
      2 * (Real.sqrt (2 * d) * 288) + deepSlotConstant d Csub Msc delta)

/-- **Part (a): the variance leg decays at the half rate in the lag.** -/
theorem slotVsumSharp_le {d : ℕ} (hd : 2 ≤ d) {Csub Msc delta : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (J : ℕ) :
    slotVsumSharp d Csub Msc delta J ≤
      vsumSourceConstant d Csub Msc delta * halfRatio ^ J := by
  have hr0 : (0 : ℝ) ≤ halfRatio := halfRatio_pos.le
  have hrJ : (0 : ℝ) ≤ halfRatio ^ J := pow_nonneg hr0 J
  have hgeom0 : (0 : ℝ) ≤ halfGeom := le_trans zero_le_one halfGeom_one_le
  have hc1 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 18 * Csub * Msc := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  have hc2 : (0 : ℝ) ≤ Real.sqrt (2 * d) * 288 := by
    have := Real.sqrt_nonneg (2 * (d : ℝ))
    positivity
  have hstep : halfRatio ^ (2 * J) ≤ halfRatio ^ J :=
    pow_le_pow_of_le_one hr0 halfRatio_lt_one.le (by omega)
  have hshallow : (3 : ℝ) ^ (-((d : ℝ) / 2) * (J : ℝ)) ≤ halfRatio ^ J :=
    le_trans (rpow_neg_mul_le_pow (one_le_half_dim hd) J) hstep
  have hunit : (3 : ℝ) ^ (-(1 : ℝ) * (J : ℝ)) ≤ halfRatio ^ J := by
    rw [rpow_neg_one_mul_eq_pow]
    exact hstep
  have hzero : slotSourceSeq d Csub Msc delta J 0 ≤
      (Real.sqrt (2 * d) * 18 * Csub * Msc + Real.sqrt (2 * d) * 288) *
        halfRatio ^ J := by
    rw [slotSourceSeq, ite_eq_left (Nat.zero_le J), Nat.sub_zero, slotSourceValue_eq]
    have h1 := mul_le_mul_of_nonneg_left hshallow hc1
    have h2 := mul_le_mul_of_nonneg_left hunit hc2
    nlinarith only [h1, h2]
  rw [slotVsumSharp, vsumSourceConstant]
  have hz := mul_le_mul_of_nonneg_left hzero hgeom0
  nlinarith only [hz, hrJ, hgeom0, hc1, hc2]

/-! ## Part (b): the bad-event leg -/

/-- The bad-event leg's source constant. -/
@[expose]
def badSourceConstant (K : ℝ) : ℝ :=
  2 * ((sourceMomentSix K / 16) ^ (4 : ℝ)⁻¹) ^ 2 +
    (sourceMomentSix K / 16) ^ (4 : ℝ)⁻¹

theorem badSourceConstant_nonneg (K : ℝ) : 0 ≤ badSourceConstant K := by
  have h := sourceMomentSix_nonneg K
  have hb : (0 : ℝ) ≤ (sourceMomentSix K / 16) ^ (4 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by linarith only [h]) _
  rw [badSourceConstant]
  nlinarith only [hb]

/-! ## Part (c): the window tail, and the common-rate comparison -/

/-- The window tail's rate is the corrected rooted rate. -/
theorem one_sub_contrastRho_half_eq (g : ℝ) :
    (1 - contrastRho g) / 2 = contrastAlpha g := by
  rw [contrastRho, contrastAlpha]
  ring

/-- **Part (c): a slower decay dominates a faster one.**  The single comparison
that puts the three legs on a common rate. -/
theorem three_rpow_neg_le {a b : ℝ} (hab : b ≤ a) :
    (3 : ℝ) ^ (-a) ≤ (3 : ℝ) ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hab])

/-- The half-rate weight in the lag, as a rate comparison. -/
theorem halfRatio_pow_le {r : ℝ} {J : ℕ} (hr : r ≤ (1 / 2 : ℝ) * (J : ℝ)) :
    halfRatio ^ J ≤ (3 : ℝ) ^ (-r) := by
  rw [← linWeight_eq_pow, linWeight]
  have hrw : -(1 / 2 : ℝ) * (J : ℝ) = -((1 / 2 : ℝ) * (J : ℝ)) := by ring
  rw [hrw]
  exact three_rpow_neg_le hr

end

end HCPolySupport.HighContrast.Quenched

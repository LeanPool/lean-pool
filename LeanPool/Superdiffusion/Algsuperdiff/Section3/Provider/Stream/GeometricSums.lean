/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval

/-!
# GeometricSums

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The geometric-sum toolkit of ABK26, Section 3.1

Sums of the shape `∑_{j = n + 1}^{m} 3 ^ (2 gamma j)` occur throughout ABK26.
The paper introduces the constant

`K_gamma = 2 (log 3) / (1 - 3 ^ (-2 gamma))`

so that `2 (log 3) ∑_{j = n + 1}^{m} 3 ^ (2 gamma j)` equals
`K_gamma (3 ^ (2 gamma m) - 3 ^ (2 gamma n))`, and records the two-sided bound
`0 ≤ K_gamma - gamma⁻¹ ≤ 4` together with the partial-sum estimates that follow
from it.

Everything here is stated for an abstract real parameter `gamma`; no part of
the probabilistic model is involved.

## Main definitions

* `Kgamma`: the constant `K_gamma` of `e.K.cgamma.def`.

## Main results

* `two_mul_log_three_mul_sum_Ioc_rpow`: the sum identity `e.K.cgamma.sum.identity`.
* `le_Kgamma`, `Kgamma_le`: the two halves of the estimate `e.K.cgamma.ineq`,
  `gamma⁻¹ ≤ K_gamma ≤ gamma⁻¹ + 4`.
* `geo_part_sum`, `geo_part_sum_le_min_inv`: the partial-sum bound
  `e.geo.part.sum`, with an explicit constant `7` in the coarse form.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.Stream

/-- The geometric-sum constant `K_gamma` of ABK26, equation `e.K.cgamma.def`. -/
noncomputable def Kgamma (gamma : ℝ) : ℝ :=
  2 * Real.log 3 / (1 - (3 : ℝ) ^ (-(2 * gamma)))

/-- The defining formula for `Kgamma`. -/
theorem Kgamma_eq (gamma : ℝ) :
    Kgamma gamma = 2 * Real.log 3 / (1 - (3 : ℝ) ^ (-(2 * gamma))) :=
  rfl

/-- The recurring prefactor `2 log 3` is positive. -/
private theorem two_mul_log_three_pos : (0 : ℝ) < 2 * Real.log 3 :=
  mul_pos (by norm_num) (Real.log_pos (by norm_num))

/-- A crude explicit upper bound for `2 log 3`. -/
private theorem two_mul_log_three_le_four : 2 * Real.log 3 ≤ 4 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith

/-- The geometric ratio `3 ^ (-2 gamma)` is below one for positive `gamma`. -/
private theorem rpow_neg_two_gamma_lt_one {gamma : ℝ} (hgamma : 0 < gamma) :
    (3 : ℝ) ^ (-(2 * gamma)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- The denominator of `Kgamma` is positive for positive `gamma`. -/
private theorem one_sub_rpow_pos {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < 1 - (3 : ℝ) ^ (-(2 * gamma)) := by
  linarith [rpow_neg_two_gamma_lt_one hgamma]

/-- `Kgamma` is positive for positive `gamma`. -/
theorem Kgamma_pos {gamma : ℝ} (hgamma : 0 < gamma) : 0 < Kgamma gamma := by
  rw [Kgamma_eq]
  exact div_pos two_mul_log_three_pos (one_sub_rpow_pos hgamma)

/-- The exponential form of the geometric ratio. -/
private theorem rpow_neg_two_gamma_eq_exp (gamma : ℝ) :
    (3 : ℝ) ^ (-(2 * gamma)) = Real.exp (-(2 * gamma * Real.log 3)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The elementary bound `1 - exp (-x) ≤ x`. -/
private theorem one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.one_sub_le_exp_neg x
  linarith

/-- The elementary bound `exp (-x) (1 + x) ≤ 1`. -/
private theorem exp_neg_mul_one_add_le_one (x : ℝ) :
    Real.exp (-x) * (1 + x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hpos : 0 < Real.exp (-x) := Real.exp_pos _
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero x)]
  have hmul : (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right h hpos.le
  rw [hcancel] at hmul
  calc Real.exp (-x) * (1 + x) = (x + 1) * Real.exp (-x) := by ring
    _ ≤ 1 := hmul

/-- Pure-real lower bound behind `e.K.cgamma.ineq`, with the geometric ratio
passed as opaque data `e`. -/
private theorem inv_le_two_mul_div_one_sub {L g e : ℝ} (hg : 0 < g) (he : e < 1)
    (h1 : 1 - e ≤ 2 * g * L) : g⁻¹ ≤ 2 * L / (1 - e) := by
  have hpos : 0 < 1 - e := by linarith
  rw [le_div_iff₀ hpos]
  calc g⁻¹ * (1 - e) ≤ g⁻¹ * (2 * g * L) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hg).le
    _ = 2 * L := by
        rw [show g⁻¹ * (2 * g * L) = g⁻¹ * g * (2 * L) by ring,
          inv_mul_cancel₀ hg.ne', one_mul]

/-- Pure-real upper bound behind `e.K.cgamma.ineq`, with the geometric ratio
passed as opaque data `e`. -/
private theorem two_mul_div_one_sub_le {L g e : ℝ} (hg : 0 < g) (he : e < 1)
    (h2 : e * (1 + 2 * g * L) ≤ 1) : 2 * L / (1 - e) ≤ g⁻¹ + 2 * L := by
  have hpos : 0 < 1 - e := by linarith
  rw [div_le_iff₀ hpos]
  have hstep : 2 * g * L ≤ (1 + 2 * g * L) * (1 - e) := by
    rw [show (1 + 2 * g * L) * (1 - e) = 1 + 2 * g * L - e * (1 + 2 * g * L) by ring]
    linarith
  calc 2 * L = g⁻¹ * (2 * g * L) := by
        rw [show g⁻¹ * (2 * g * L) = g⁻¹ * g * (2 * L) by ring,
          inv_mul_cancel₀ hg.ne', one_mul]
    _ ≤ g⁻¹ * ((1 + 2 * g * L) * (1 - e)) :=
        mul_le_mul_of_nonneg_left hstep (inv_pos.mpr hg).le
    _ = (g⁻¹ + 2 * L) * (1 - e) := by
        rw [show g⁻¹ * ((1 + 2 * g * L) * (1 - e)) =
            (g⁻¹ + g⁻¹ * g * (2 * L)) * (1 - e) by ring,
          inv_mul_cancel₀ hg.ne', one_mul]

/-- The lower half of ABK26's `e.K.cgamma.ineq`. -/
theorem le_Kgamma {gamma : ℝ} (hgamma : 0 < gamma) : gamma⁻¹ ≤ Kgamma gamma := by
  have h1 : 1 - (3 : ℝ) ^ (-(2 * gamma)) ≤ 2 * gamma * Real.log 3 := by
    rw [rpow_neg_two_gamma_eq_exp]
    exact one_sub_exp_neg_le _
  rw [Kgamma_eq]
  exact inv_le_two_mul_div_one_sub hgamma (rpow_neg_two_gamma_lt_one hgamma) h1

/-- The sharp form of the upper half of `e.K.cgamma.ineq`. -/
theorem Kgamma_le_inv_add_two_mul_log {gamma : ℝ} (hgamma : 0 < gamma) :
    Kgamma gamma ≤ gamma⁻¹ + 2 * Real.log 3 := by
  have h2 : (3 : ℝ) ^ (-(2 * gamma)) * (1 + 2 * gamma * Real.log 3) ≤ 1 := by
    rw [rpow_neg_two_gamma_eq_exp]
    exact exp_neg_mul_one_add_le_one _
  rw [Kgamma_eq]
  exact two_mul_div_one_sub_le hgamma (rpow_neg_two_gamma_lt_one hgamma) h2

/-- The upper half of ABK26's `e.K.cgamma.ineq` with the paper's constant. -/
theorem Kgamma_le {gamma : ℝ} (hgamma : 0 < gamma) : Kgamma gamma ≤ gamma⁻¹ + 4 := by
  have h := Kgamma_le_inv_add_two_mul_log hgamma
  have h4 := two_mul_log_three_le_four
  linarith

/-- The real power `3 ^ (2 gamma j)` at an integer scale is an integer power of
the ratio `3 ^ (2 gamma)`. -/
private theorem rpow_intCast_mul (gamma : ℝ) (j : ℤ) :
    (3 : ℝ) ^ (2 * gamma * (j : ℝ)) = ((3 : ℝ) ^ (2 * gamma)) ^ (j : ℤ) := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_intCast]

/-- Cancellation of a nonzero factor across a quotient. -/
private theorem div_mul_mul_cancel {a b c : ℝ} (hc : c ≠ 0) :
    a / c * (c * b) = a * b := by
  rw [div_mul_eq_mul_div, mul_comm c b, ← mul_assoc, mul_div_assoc, div_self hc,
    mul_one]

/-- Telescoping form of the finite geometric sum over an integer interval. -/
private theorem one_sub_inv_mul_sum_zpow {r : ℝ} (hr : r ≠ 0) {n m : ℤ}
    (hnm : n ≤ m) :
    (1 - r⁻¹) * ∑ j ∈ Finset.Ioc n m, r ^ j = r ^ m - r ^ n := by
  induction m, hnm using Int.leInduction with
  | base => simp
  | succ k hk ih =>
      have hins : Finset.Ioc n (k + 1) = insert (k + 1) (Finset.Ioc n k) := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnotmem : (k + 1) ∉ Finset.Ioc n k := by
        simp only [Finset.mem_Ioc]
        omega
      rw [hins, Finset.sum_insert hnotmem, mul_add, ih, zpow_add_one₀ hr]
      rw [show (1 - r⁻¹) * (r ^ k * r) = r ^ k * r - r⁻¹ * r * r ^ k by ring,
        inv_mul_cancel₀ hr, one_mul]
      ring

/-- The geometric-sum identity in terms of an abstract ratio `r`. -/
private theorem two_mul_log_three_mul_sum_zpow {r : ℝ} (hr : r ≠ 0)
    (hne : (1 : ℝ) - r⁻¹ ≠ 0) {n m : ℤ} (hnm : n ≤ m) :
    2 * Real.log 3 / (1 - r⁻¹) * (r ^ m - r ^ n) =
      2 * Real.log 3 * ∑ j ∈ Finset.Ioc n m, r ^ j := by
  rw [← one_sub_inv_mul_sum_zpow hr hnm]
  exact div_mul_mul_cancel hne

/-- ABK26's `e.K.cgamma.sum.identity`. -/
theorem two_mul_log_three_mul_sum_Ioc_rpow {gamma : ℝ} (hgamma : 0 < gamma)
    {n m : ℤ} (hnm : n ≤ m) :
    2 * Real.log 3 * ∑ j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (j : ℝ)) =
      Kgamma gamma *
        ((3 : ℝ) ^ (2 * gamma * (m : ℝ)) - (3 : ℝ) ^ (2 * gamma * (n : ℝ))) := by
  have hr : ((3 : ℝ) ^ (2 * gamma)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have he : (3 : ℝ) ^ (-(2 * gamma)) = ((3 : ℝ) ^ (2 * gamma))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  have hne : (1 : ℝ) - ((3 : ℝ) ^ (2 * gamma))⁻¹ ≠ 0 := by
    rw [← he]
    exact ne_of_gt (one_sub_rpow_pos hgamma)
  have hsum : ∑ j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (j : ℝ)) =
      ∑ j ∈ Finset.Ioc n m, ((3 : ℝ) ^ (2 * gamma)) ^ (j : ℤ) :=
    Finset.sum_congr rfl fun j _ => rpow_intCast_mul gamma j
  rw [Kgamma_eq, he, hsum, rpow_intCast_mul gamma m, rpow_intCast_mul gamma n]
  exact (two_mul_log_three_mul_sum_zpow hr hne hnm).symm

/-- The counting bound behind the second term of `e.geo.part.sum`. -/
private theorem sum_Ioc_rpow_le_card_mul {gamma : ℝ} (hgamma : 0 < gamma)
    {n m : ℤ} (hnm : n ≤ m) :
    ∑ j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (j : ℝ)) ≤
      ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by
  have hcard : ((Finset.Ioc n m).card : ℝ) = (m : ℝ) - (n : ℝ) := by
    have hz := congrArg (fun z : ℤ => (z : ℝ)) (Int.card_Ioc_of_le n m hnm)
    push_cast at hz
    exact hz
  calc ∑ j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (j : ℝ))
      ≤ ∑ _j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hjm : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hj).2
        exact mul_le_mul_of_nonneg_left hjm (by linarith)
    _ = ((Finset.Ioc n m).card : ℝ) * (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by rw [hcard]

/-- ABK26's `e.geo.part.sum`, first inequality. -/
theorem geo_part_sum {gamma : ℝ} (hgamma : 0 < gamma) {n m : ℤ} (hnm : n ≤ m) :
    2 * Real.log 3 * ∑ j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (j : ℝ)) ≤
      min (Kgamma gamma) (2 * Real.log 3 * ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by
  rcases le_total (Kgamma gamma) (2 * Real.log 3 * ((m : ℝ) - (n : ℝ))) with h | h
  · rw [min_eq_left h, two_mul_log_three_mul_sum_Ioc_rpow hgamma hnm]
    have hn : (0 : ℝ) < (3 : ℝ) ^ (2 * gamma * (n : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact mul_le_mul_of_nonneg_left (by linarith) (Kgamma_pos hgamma).le
  · rw [min_eq_right h]
    calc 2 * Real.log 3 * ∑ j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (j : ℝ))
        ≤ 2 * Real.log 3 *
            (((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * gamma * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_rpow_le_card_mul hgamma hnm)
            two_mul_log_three_pos.le
      _ = 2 * Real.log 3 * ((m : ℝ) - (n : ℝ)) *
            (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by ring

/-- ABK26's `e.geo.part.sum`, second inequality, with the explicit constant
`7`. -/
theorem geo_part_sum_le_min_inv {gamma : ℝ} (hgamma : 0 < gamma)
    (hquarter : gamma ≤ 1 / 4) {n m : ℤ} (hnm : n ≤ m) :
    2 * Real.log 3 * ∑ j ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * gamma * (j : ℝ)) ≤
      7 * min gamma⁻¹ ((m : ℝ) - (n : ℝ)) * (3 : ℝ) ^ (2 * gamma * (m : ℝ)) := by
  refine (geo_part_sum hgamma hnm).trans ?_
  have ht : (0 : ℝ) < (3 : ℝ) ^ (2 * gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine mul_le_mul_of_nonneg_right ?_ ht.le
  have hmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have hginv : 0 < gamma⁻¹ := inv_pos.mpr hgamma
  have hgi : gamma⁻¹ * gamma = 1 := inv_mul_cancel₀ hgamma.ne'
  have h4 : (4 : ℝ) ≤ gamma⁻¹ := by nlinarith [hgi, hginv, hgamma, hquarter]
  rcases le_total gamma⁻¹ ((m : ℝ) - (n : ℝ)) with h | h
  · rw [min_eq_left h]
    refine (min_le_left _ _).trans ?_
    have hK := Kgamma_le hgamma
    linarith
  · rw [min_eq_right h]
    refine (min_le_right _ _).trans ?_
    calc 2 * Real.log 3 * ((m : ℝ) - (n : ℝ)) ≤ 4 * ((m : ℝ) - (n : ℝ)) :=
          mul_le_mul_of_nonneg_right two_mul_log_three_le_four hmn
      _ ≤ 7 * ((m : ℝ) - (n : ℝ)) := by linarith

end Algsuperdiff.Section3.Provider.Stream

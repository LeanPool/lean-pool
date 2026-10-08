/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeConcentration

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeGridCount

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scale-`n` cubes centred in `□_m`

The concentration-for-sums condition supplied by unit range of dependence is
stated for the family of standard aligned cubes of scale `n` whose centres lie in
`□_m`, and its fluctuation scale is `3^(-ν(m-n))` with `ν = d/2`.  This file
identifies that family as an explicit finite index set and counts it: there are
`3^(d(m-n))` such cubes, so the reciprocal square root of their number is exactly
`3^(-ν(m-n))`.

The count is elementary.  A centre `3^n w` lies in `□_m` exactly when each
coordinate of `w` is strictly between `±3^(m-n)/2`; since `3^(m-n)` is an odd
integer `2h+1`, that is exactly `|w i| ≤ h`, and each coordinate therefore ranges
over `2h + 1 = 3^(m-n)` values.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

/-! ## The half width -/

/-- The largest index coordinate of a scale-`n` cube centred in `□_m`. -/
@[expose]
def centredHalfWidth (n m : ℤ) : ℤ := ((3 : ℤ) ^ (m - n).toNat - 1) / 2

/-- `3^k` is odd, in the form the count uses. -/
theorem two_mul_half_add_one (k : ℕ) : 2 * (((3 : ℤ) ^ k - 1) / 2) + 1 = 3 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hpos : (0 : ℤ) < 3 ^ k := by positivity
      rw [pow_succ]
      set a : ℤ := (3 : ℤ) ^ k with hadef
      clear_value a
      omega

theorem two_mul_centredHalfWidth_add_one (n m : ℤ) :
    2 * centredHalfWidth n m + 1 = (3 : ℤ) ^ (m - n).toNat :=
  two_mul_half_add_one _

theorem centredHalfWidth_nonneg (n m : ℤ) : 0 ≤ centredHalfWidth n m := by
  have hkey := two_mul_centredHalfWidth_add_one n m
  have hpos : (0 : ℤ) < 3 ^ (m - n).toNat := by positivity
  omega

/-! ## The index set -/

/-- The indices of the standard aligned cubes of scale `n` whose centres lie in
`□_m`. -/
@[expose]
def centredIndexFinset (d : ℕ) (n m : ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d =>
    Finset.Icc (-centredHalfWidth n m) (centredHalfWidth n m)

theorem mem_centredIndexFinset {d : ℕ} {n m : ℤ} {w : Fin d → ℤ} :
    w ∈ centredIndexFinset d n m ↔
      ∀ i, -centredHalfWidth n m ≤ w i ∧ w i ≤ centredHalfWidth n m := by
  rw [centredIndexFinset, Fintype.mem_piFinset]
  exact forall_congr' fun _ => Finset.mem_Icc

/-- The integer form of the centring condition. -/
private theorem mem_Icc_iff_real {h z : ℤ} :
    (-(h : ℝ) - 1 / 2 < (z : ℝ) ∧ (z : ℝ) < (h : ℝ) + 1 / 2) ↔ (-h ≤ z ∧ z ≤ h) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hcon
      push Not at hcon
      have hz : z ≤ -h - 1 := by omega
      have hzr : (z : ℝ) ≤ -(h : ℝ) - 1 := by exact_mod_cast hz
      linarith only [h1, hzr]
    · by_contra hcon
      push Not at hcon
      have hz : h + 1 ≤ z := by omega
      have hzr : (h : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz
      linarith only [h2, hzr]
  · rintro ⟨h1, h2⟩
    have hl : -(h : ℝ) ≤ (z : ℝ) := by exact_mod_cast h1
    have hr : (z : ℝ) ≤ (h : ℝ) := by exact_mod_cast h2
    exact ⟨by linarith only [hl], by linarith only [hr]⟩

/-- **The index set is exactly the centring condition.** -/
theorem mem_centredIndexFinset_iff {d : ℕ} {n m : ℤ} (hnm : n ≤ m)
    {w : Fin d → ℤ} :
    w ∈ centredIndexFinset d n m ↔ standardCellCenter n w ∈ centeredCube d m := by
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  set K : ℕ := (m - n).toNat with hKdef
  have hcast : (K : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  have hmn : m = n + (K : ℤ) := by omega
  have hLreal : (((3 : ℤ) ^ K : ℤ) : ℝ) = (3 : ℝ) ^ ((K : ℕ) : ℤ) := by
    push_cast
    rw [zpow_natCast]
  have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ n * (((3 : ℤ) ^ K : ℤ) : ℝ) := by
    rw [hLreal, hmn, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hodd : (((3 : ℤ) ^ K : ℤ) : ℝ) = 2 * (centredHalfWidth n m : ℝ) + 1 := by
    have h := two_mul_centredHalfWidth_add_one n m
    rw [← hKdef] at h
    exact_mod_cast h.symm
  have hL1 : -(1 / 2 : ℝ) * (3 : ℝ) ^ m
      = (3 : ℝ) ^ n * (-(centredHalfWidth n m : ℝ) - 1 / 2) := by
    rw [hpow, hodd]
    ring
  have hL2 : (1 / 2 : ℝ) * (3 : ℝ) ^ m
      = (3 : ℝ) ^ n * ((centredHalfWidth n m : ℝ) + 1 / 2) := by
    rw [hpow, hodd]
    ring
  rw [mem_centredIndexFinset, Recurrence.mem_centeredCube_iff]
  refine forall_congr' fun i => ?_
  have hcentre : standardCellCenter n w i = (3 : ℝ) ^ n * (w i : ℝ) := rfl
  constructor
  · intro hw
    obtain ⟨g1, g2⟩ := mem_Icc_iff_real.2 hw
    rw [hcentre, hL1, hL2]
    exact ⟨mul_lt_mul_of_pos_left g1 h3n, mul_lt_mul_of_pos_left g2 h3n⟩
  · rintro ⟨h1, h2⟩
    rw [hcentre, hL1] at h1
    rw [hcentre, hL2] at h2
    exact mem_Icc_iff_real.1
      ⟨lt_of_mul_lt_mul_left h1 h3n.le, lt_of_mul_lt_mul_left h2 h3n.le⟩

/-! ## The count -/

private theorem toNat_three_pow (k : ℕ) : ((3 : ℤ) ^ k).toNat = 3 ^ k := by
  have h1 : (((3 : ℤ) ^ k).toNat : ℤ) = (3 : ℤ) ^ k :=
    Int.toNat_of_nonneg (by positivity)
  have h2 : ((3 ^ k : ℕ) : ℤ) = (3 : ℤ) ^ k := by push_cast; ring
  exact_mod_cast h1.trans h2.symm

/-- **There are `3^(d(m-n))` standard aligned cubes of scale `n` centred in
`□_m`.** -/
theorem card_centredIndexFinset (d : ℕ) (n m : ℤ) :
    (centredIndexFinset d n m).card = 3 ^ (d * (m - n).toNat) := by
  have hcard : (Finset.Icc (-centredHalfWidth n m) (centredHalfWidth n m)).card
      = 3 ^ (m - n).toNat := by
    rw [Int.card_Icc]
    have hkey := two_mul_centredHalfWidth_add_one n m
    have htoNat : (centredHalfWidth n m + 1 - -centredHalfWidth n m).toNat
        = ((3 : ℤ) ^ (m - n).toNat).toNat := by omega
    rw [htoNat, toNat_three_pow]
  rw [centredIndexFinset, Fintype.card_piFinset]
  simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [mul_comm]

theorem centredIndexFinset_nonempty (d : ℕ) (n m : ℤ) :
    (centredIndexFinset d n m).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [mem_centredIndexFinset]
  intro _
  have := centredHalfWidth_nonneg n m
  omega

/-- **The fluctuation scale of the family is `3^(ν(m-n))` with `ν = d/2`.** -/
theorem sqrt_card_centredIndexFinset (d : ℕ) {n m : ℤ} (hnm : n ≤ m) :
    Real.sqrt (((centredIndexFinset d n m).card : ℕ) : ℝ)
      = (3 : ℝ) ^ ((d : ℝ) / 2 * ((m : ℝ) - (n : ℝ))) := by
  have hcast : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  have hreal : (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    have hstep := congrArg (fun z : ℤ => (z : ℝ)) hcast
    push_cast at hstep
    exact hstep
  rw [card_centredIndexFinset]
  have hbase : ((3 ^ (d * (m - n).toNat) : ℕ) : ℝ)
      = (3 : ℝ) ^ ((d : ℝ) * (((m - n).toNat : ℕ) : ℝ)) := by
    rw [show (d : ℝ) * (((m - n).toNat : ℕ) : ℝ) = ((d * (m - n).toNat : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast]
    push_cast
    ring
  rw [hbase, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hreal]
  congr 1
  ring

/-! ## The printed form of the concentration estimate -/

end

end Quenched
end HighContrast
end HCPolySupport

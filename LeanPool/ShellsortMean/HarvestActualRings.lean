/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.RoughGapEndpoint
public import LeanPool.ShellsortMean.RoughGapFarInteraction

/-! Finite dyadic decomposition of the actual physical error at the half-integer rank cut. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestActualRings
open Finset RoughGapEndpoint

/-- Floor of distance from the cut T-1/2. Thus twice the exact distance is 2*depth+1. -/
def depth (T i : ℕ) : ℕ := if i < T then T - 1 - i else i - T

/-- The radius of the specified dyadic level at the initial scale `H`. -/
def rad (H k : ℕ) := 2 ^ k * H

private theorem power_ge (j : ℕ) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => decide
  | succ j ih => rw [pow_succ]; omega

theorem depth_lt {n T : ℕ} (ht : T ≤ n) (i : Fin n) : depth T i.val < n := by
  unfold depth
  split <;> omega

theorem rad_large {H : ℕ} (hp : 0 < H) (n : ℕ) : n < rad H n := by
  have u := Nat.mul_le_mul_left (2 ^ n) hp
  rw [Nat.mul_one] at u
  have t := power_ge n
  unfold rad
  omega

theorem cover {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (i : Fin n) :
    ∃ k, depth T i.val < rad H k :=
  ⟨n, (depth_lt ht i).trans (rad_large hp n)⟩

/-- First dyadic ball containing a slot. A finite index is sufficient even with truncated end
rings. -/
def band {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (i : Fin n) : Fin (n + 1) :=
  ⟨Nat.find (cover ht hp i), Nat.lt_succ_of_le (Nat.find_min' (cover ht hp i) ((depth_lt ht
    i).trans (rad_large hp n)))⟩

theorem band_upper {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (i : Fin n) :
    depth T i.val < rad H (band ht hp i).val := Nat.find_spec (cover ht hp i)

theorem band_lower {n T H j : ℕ} (ht : T ≤ n) (hp : 0 < H) (i : Fin n)
    (hj : j < (band ht hp i).val) : rad H j ≤ depth T i.val :=
  Nat.le_of_not_gt (Nat.find_min (cover ht hp i) hj)

private theorem rad_mono (H : ℕ) {j k : ℕ} (h : j ≤ k) : rad H j ≤ rad H k := by
  exact Nat.mul_le_mul_right H (Nat.pow_le_pow_right (by decide : 0 < 2) h)

/-- The left endpoint of a cut-centered interval, clipped at zero. -/
def start (T R : ℕ) := T - R

/-- A half-open interval with clipped start and prescribed length; it may extend beyond n. -/
theorem ball_support {T i R : ℕ} (h : depth T i < R) :
    start T R ≤ i ∧ i < start T R + 2 * R := by
  unfold start
  unfold depth at h
  split at h <;> omega

/-- All earlier bands together fit in a *single* interval. -/
theorem merged_support {n T H k : ℕ} (ht : T ≤ n) (hp : 0 < H) (i : Fin n)
    (hk : (band ht hp i).val ≤ k) :
    start T (rad H k) ≤ i.val ∧ i.val < start T (rad H k) + 2 * rad H k :=
  ball_support ((band_upper ht hp i).trans_le (rad_mono _ hk))

/-- The threshold error vector restricted to a single dyadic ring. -/
def ringVec {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : Fin (n + 1)) (i : Fin n) : ℤ :=
  if k = band ht hp i then slotError p T i else 0

theorem partition {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n) (i : Fin n) :
    ∑ k, ringVec ht hp p k i = slotError p T i := by simp [ringVec]

theorem weighted_partition {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (w : Fin (n + 1) → ℤ) :
    ∑ k, w k * ∑ i, |ringVec ht hp p k i| =
    ∑ i, w (band ht hp i) * |slotError p T i| := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ringVec, abs_ite, mul_ite]

theorem distance_moment {n : ℕ} (p : RankPlacement n) (T : ℕ) :
    ∑ i : Fin n, (2 * (depth T i.val : ℤ) + 1) * |slotError p T i| =
    2 * cutMoment p T := by
  have eqn (i : Fin n) : (2 * (depth T i.val : ℤ) + 1) * |slotError p T i| =
        2 * ((i.val : ℤ) - T) * slotError p T i + slotError p T i := by
    by_cases hi : i.val < T <;> by_cases hl : i ∈ thresholdSet p T
    all_goals simp [depth, slotError, hi, hl]
    all_goals omega
  simp_rw [eqn]
  rw [sum_add_distrib, sum_slotError, add_zero]
  unfold cutMoment
  rw [mul_sum]
  simp [slotError, mul_assoc]

theorem outer_radius {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (i : Fin n) (pos : 0 < (band ht hp
  i).val) :
    rad H (band ht hp i).val ≤ 2 * depth T i.val := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
  have lo := band_lower ht hp i (j := j) (by omega)
  rw [hj]
  unfold rad at *
  rw [pow_succ]
  nlinarith

/-- The total support-length charge, with the inner core paid once. -/
theorem length_mass {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n) :
    ∑ k : Fin (n + 1), (2 * (rad H k.val : ℤ)) * ∑ i, |ringVec ht hp p k i| ≤
      2 * H * (∑ i, |slotError p T i| : ℤ) + 4 * cutMoment p T := by
  rw [weighted_partition]
  have hu (i : Fin n) : (rad H (band ht hp i).val : ℤ) ≤ H + 2 * (depth T i.val : ℤ) + 1 := by
    by_cases h : (band ht hp i).val = 0
    · simp [h, rad]; omega
    · have e := outer_radius ht hp i (Nat.pos_of_ne_zero h)
      exact_mod_cast (show rad H (band ht hp i).val ≤ H + 2 * depth T i.val + 1 by omega)
  have eqmom := distance_moment p T
  calc
    _ ≤ ∑ i : Fin n, (2 * (H : ℤ) + 2 * (2 * (depth T i.val : ℤ) + 1)) * |slotError p T i| := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith [hu i]
    _ = _ := by
      simp_rw [add_mul, mul_assoc (2 : ℤ) (2 * _ + 1)]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, eqmom]
      ring

/-- The threshold error contributed by the rings up to the given level. -/
def mergedVec {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : ℕ) (i : Fin n) : ℤ :=
  if (band ht hp i).val ≤ k then slotError p T i else 0

theorem merge_exact {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : ℕ) (i : Fin n) :
    ∑ j ∈ univ.filter (fun j : Fin (n + 1) => j.val ≤ k), ringVec ht hp p j i =
      mergedVec ht hp p k i := by
  simp [ringVec, mergedVec]

theorem merged_unit {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : ℕ) (i : Fin n) : |mergedVec ht hp p k i| ≤ 1 := by
  unfold mergedVec slotError
  split_ifs <;> decide

theorem merged_nonzero_support {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : ℕ) (i : Fin n) (hn : mergedVec ht hp p k i ≠ 0) :
    start T (rad H k) ≤ i.val ∧ i.val < start T (rad H k) + 2 * rad H k := by
  apply merged_support ht hp i
  by_contra hn'
  simp [mergedVec, hn'] at hn

/-- Pad a physical array by zero beyond the end of a support interval. -/
def pad {n L : ℕ} (a : ℕ) (u : Fin n → ℝ) (j : Fin L) : ℝ :=
  if v : a + j.val < n then u ⟨a + j.val, v⟩ else 0

theorem pad_sum {n L : ℕ} (a : ℕ) (u : Fin n → ℝ)
    (support : ∀ i, u i ≠ 0 → a ≤ i.val ∧ i.val < a + L) :
    ∑ i, u i = ∑ j : Fin L, pad a u j := by
  apply sum_bij_ne_zero (fun i _ nz => (⟨i.val - a, by have := support i nz; omega⟩ : Fin L))
  · simp
  · intro i _ hi j _ hj eq
    have h1 := support i hi
    have h2 := support j hj
    have h3 := congrArg Fin.val eq
    dsimp at h3
    apply Fin.ext
    omega
  · intro j _ nz
    unfold pad at nz
    split at nz
    · rename_i h
      exact ⟨⟨a + j.val, h⟩, mem_univ _, nz, Fin.ext (by simp)⟩
    · contradiction
  · intro i _ nz
    have h := (support i nz).1
    have eq : a + (i.val - a) = i.val := by omega
    simp [pad, eq]

open RoughGapFarInteraction in
theorem centered_pad {n L h : ℕ} (hh : 0 < h) (a : ℕ) (u : Fin n → ℝ)
    (support : ∀ i, u i ≠ 0 → a ≤ i.val ∧ i.val < a + L) (r : Fin h) :
    centered (intervalResidue hh 0) u r =
      centered (intervalResidue hh a) (fun j : Fin L => pad a u j) r := by
  unfold centered bucket
  rw [pad_sum a u support]
  let v (i : Fin n) := if intervalResidue hh 0 i = r then u i else 0
  have vs (i : Fin n) (nz : v i ≠ 0) := support i (by
    by_contra zero
    simp [v, zero] at nz)
  change (∑ i, v i) - _ = _
  rw [pad_sum a v vs]
  congr 1
  apply sum_congr rfl
  intro j _
  by_cases hj : a + j.val < n
  · simp [pad, hj, v, intervalResidue]
  · simp [pad, hj]

open RoughGapFarInteraction in
theorem actual_far_cross {n T H g : ℕ} (ht : T ≤ n) (hp : 0 < H) (hg : 0 < g)
    (p : RankPlacement n) (j : ℕ) (k : Fin (n + 1)) :
    |2 * (g : ℝ) * ∑ r, centered (intervalResidue hg 0)
      (fun i => (mergedVec ht hp p j i : ℝ)) r *
      centered (intervalResidue hg 0) (fun i => (ringVec ht hp p k i : ℝ)) r| ≤
      (4 * g + 8 * (2 * rad H j : ℕ)) * ∑ i, |(ringVec ht hp p k i : ℝ)| := by
  let u (i : Fin n) := (mergedVec ht hp p j i : ℝ)
  let a := start T (rad H j)
  let L := 2 * rad H j
  have hs (i : Fin n) (nz : u i ≠ 0) : a ≤ i.val ∧ i.val < a + L := by
    apply merged_nonzero_support ht hp p j i
    dsimp [u] at nz
    exact_mod_cast nz
  have hu (t : Fin L) : |pad a u t| ≤ 1 := by
    unfold pad
    split
    · rename_i hyp
      dsimp [u]
      exact_mod_cast merged_unit ht hp p j ⟨a + t.val, hyp⟩
    · norm_num
  change |2 * (g : ℝ) * ∑ r, centered (intervalResidue hg 0) u r * _| ≤ _
  simp_rw [centered_pad hg a u hs]
  exact far_inner_outer hg a _ hu _ _

open RoughGapFarInteraction in
theorem actual_separation {n T H j m : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (k : Fin (n + 1)) (hk : k.val = j + m) (hm : 0 < m) (i : Fin n)
    (nz : ringVec ht hp p k i ≠ 0) :
    (2 * rad H j : ℕ) ≤ 4 * (1 / (2 : ℝ) ^ m) * (depth T i.val : ℝ) := by
  have hb : k = band ht hp i := by
    by_contra ne
    simp [ringVec, ne] at nz
  have pos : 0 < (band ht hp i).val := by rw [← hb, hk]; omega
  have ub := outer_radius ht hp i pos
  rw [← hb, hk] at ub
  apply dyadic_interval_separation j m (H : ℝ)
  · simp [rad, mul_assoc]
  · exact_mod_cast ub







theorem real_slot_mass {n T H : ℕ} (ht : T ≤ n) (hp : 0 < H) (p : RankPlacement n)
    (i : Fin n) : ∑ k, |(ringVec ht hp p k i : ℝ)| = |(slotError p T i : ℝ)| := by
  simp [ringVec, abs_ite]

theorem real_distance_le {n : ℕ} (p : RankPlacement n) (T : ℕ) :
    (∑ i : Fin n, (depth T i.val : ℝ) * |(slotError p T i : ℝ)|) ≤ (cutMoment p T : ℝ) := by
  have eqmom :
      (∑ i : Fin n, (2 * (depth T i.val : ℝ) + 1) * |(slotError p T i : ℝ)|) =
      2 * (cutMoment p T : ℝ) := by exact_mod_cast distance_moment p T
  have hmass : 0 ≤ ∑ i, |(slotError p T i : ℝ)| := sum_nonneg (fun i _ => abs_nonneg _)
  simp_rw [add_mul, one_mul, mul_assoc] at eqmom
  rw [sum_add_distrib, ← mul_sum] at eqmom
  linarith

/-- Sum one per-outer-ring charge after all earlier rings have already been merged.
The term proportional to interval length is paid from the actual cut moment. -/
theorem sum_far_charges {n T H m : ℕ} (ht : T ≤ n) (hp : 0 < H) (hm : 0 < m)
    (p : RankPlacement n) (A B : ℝ) (ha : 0 ≤ A) (hb : 0 ≤ B)
    (charge : Fin (n + 1) → ℝ)
    (perRing : ∀ k : Fin (n + 1), m ≤ k.val →
      charge k ≤ (A + B * (2 * rad H (k.val - m) : ℕ)) * ∑ i, |(ringVec ht hp p k i : ℝ)|) :
    ∑ k ∈ univ.filter (fun k : Fin (n + 1) => m ≤ k.val), charge k ≤
      A * ∑ i, |(slotError p T i : ℝ)| + (4 * B * (1 / (2 : ℝ) ^ m)) * (cutMoment p T : ℝ) := by
  let C := 4 * B * (1 / (2 : ℝ) ^ m)
  have hc : 0 ≤ C := by dsimp [C]; positivity
  let f (k : Fin (n + 1)) (i : Fin n) :=
    (A + C * (depth T i.val : ℝ)) * |(ringVec ht hp p k i : ℝ)|
  have fn (k : Fin (n + 1)) (i : Fin n) : 0 ≤ f k i := by
    dsimp [f]; positivity
  calc
    _ ≤ ∑ k ∈ univ.filter (fun k : Fin (n + 1) => m ≤ k.val), ∑ i, f k i := by
      apply sum_le_sum
      intro k hk
      have hkm := (mem_filter.mp hk).2
      apply (perRing k hkm).trans
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      by_cases hz : ringVec ht hp p k i = 0
      · simp [f, hz]
      · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have sep := actual_separation (j := k.val - m) ht hp p k (by omega) hm i hz
        have bm := mul_le_mul_of_nonneg_left sep hb
        dsimp [C]; linarith only [bm, show B * (4 * (1 / (2 : ℝ) ^ m) * (depth T i.val : ℝ)) =
          4 * B * (1 / (2 : ℝ) ^ m) * (depth T i.val : ℝ) by ring]
    _ ≤ ∑ k, ∑ i, f k i := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
      (fun k _ _ => sum_nonneg (fun i _ => fn k i))
    _ = A * ∑ i, |(slotError p T i : ℝ)| +
        C * ∑ i, (depth T i.val : ℝ) * |(slotError p T i : ℝ)| := by
      rw [sum_comm]
      simp only [f, ← mul_sum, real_slot_mass, add_mul, mul_assoc, sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (real_distance_le p T) hc)


end Shellsort.HarvestActualRings

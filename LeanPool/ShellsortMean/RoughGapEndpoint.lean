/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ChainCoordinates
public import LeanPool.ShellsortMean.RoughGapScaleAssembly

/-! One ordinary gap pass on an actual rank placement: an exact quadratic
identity for each cut, including the signed endpoint phase of each chain. -/
@[expose] public noncomputable section
namespace Shellsort.RoughGapEndpoint
open Finset
open scoped BigOperators

/-- Signed discrepancy in a physical residue before the pass. -/
def residueError {n : ℕ} (p : RankPlacement n) (h T r : ℕ) : ℤ :=
  (chainLowerCount (thresholdSet p T) h r : ℤ) - residuePrefixCount h r T

/-- The doubled centered offset of a residue at a rank cut. -/
def phase (h T r : ℕ) : ℤ :=
  2 * ((r : ℤ) + h * residuePrefixCount h r T - T) - h

theorem phase_abs_le {h r : ℕ} (T : ℕ) (hh : 0 < h) (hr : r < h) :
    |phase h T r| ≤ (h : ℤ) := by
  have hb := counted_residual_bounds h r T hh hr
  unfold phase
  apply abs_le.mpr
  omega

theorem ideal_ord {h r : ℕ} (T v : ℕ) (hh : 0 < h) (hr : r < h) :
    r + h * v < T ↔ v < residuePrefixCount h r T := by
  have hb := counted_residual_bounds h r T hh hr
  constructor
  · intro hv
    by_contra! hn
    have hm := Nat.mul_le_mul_left h hn
    omega
  · intro hv
    have hm := Nat.mul_le_mul_left h (Nat.succ_le_of_lt hv)
    rw [Nat.mul_succ] at hm
    omega

theorem prefixSum {M : Type*} [AddCommMonoid M] {b L : ℕ} (hb : b ≤ L) (f : ℕ → M) :
    (∑ v : Fin L, if v.val < b then f v.val else 0) = ∑ v ∈ range b, f v := by
  rw [Fin.sum_univ_eq_sum_range (fun v => if v < b then f v else 0)]
  induction L, hb using Nat.le_induction with
  | base =>
    apply sum_congr rfl
    intro v hv
    simp [mem_range.mp hv]
  | succ l hl ih =>
    rw [sum_range_succ, ih]
    simp [not_lt.mpr hl]

private theorem doublePrefix (h r T b : ℕ) :
    2 * (∑ v ∈ range b, ((r : ℤ) + h * v - T)) =
      (2 * (r : ℤ) - 2 * T - h) * b + h * (b : ℤ) ^ 2 := by
  induction b with
  | zero => simp
  | succ b ih => rw [sum_range_succ, mul_add, ih]; push_cast; ring

theorem lower_at_coord {n h : ℕ} (p : RankPlacement n) (hh : 0 < h)
    (T : ℕ) (r : Fin h) (v : Fin (sourceTrialLength (n / h) (n % h) r.val)) :
    (positionChainEquiv n h hh).symm ⟨r, v⟩ ∈ thresholdSet (gapSort p h) T ↔
      v.val < chainLowerCount (thresholdSet p T) h r.val := by
  rw [gapSort_threshold_commutes]
  simp only [lowerStep, mem_filter, mem_univ, true_and, chainOrdinal_eq_div _ hh]
  rw [positionChainEquiv_symm_residue, positionChainEquiv_symm_val]
  simp [Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt r.isLt]

/-- Centered moment in physical slot coordinates. Total discrepancy is zero,
so centering at T or T−1/2 gives the same integer. -/
def cutMoment {n : ℕ} (p : RankPlacement n) (T : ℕ) : ℤ :=
  ∑ i : Fin n, ((i.val : ℤ) - T) *
    ((if i ∈ thresholdSet p T then 1 else 0) - (if i.val < T then 1 else 0))

private theorem coordMoment {n h : ℕ} (p : RankPlacement n) (T : ℕ) (hT : T ≤ n)
    (hh : 0 < h) (r : Fin h) :
    2 * (∑ v : Fin (sourceTrialLength (n / h) (n % h) r.val),
      ((r.val : ℤ) + h * v.val - T) *
      ((if v.val < chainLowerCount (thresholdSet p T) h r.val then 1 else 0) -
       (if v.val < residuePrefixCount h r.val T then 1 else 0))) =
      (h : ℤ) * residueError p h T r.val ^ 2 + phase h T r.val * residueError p h T r.val := by
  let b := chainLowerCount (thresholdSet p T) h r.val
  let a := residuePrefixCount h r.val T
  have bl : b ≤ sourceTrialLength (n / h) (n % h) r.val := by
    rw [← actual_chain_length n h hh r, chainPositions_card]
    exact chainLowerCount_le_length _ _ _
  have al : a ≤ sourceTrialLength (n / h) (n % h) r.val := by
    rw [← actual_chain_length n h hh r, chainPositions_card]
    unfold a residuePrefixCount
    exact sum_le_sum_of_subset_of_nonneg (range_mono hT) (by intros; positivity)
  let f := fun v : ℕ => ((r.val : ℤ) + h * v - T)
  change 2 * (∑ v : Fin _, f v.val * ((if v.val < b then 1 else 0) -
    (if v.val < a then 1 else 0))) = _
  simp_rw [mul_sub, mul_ite, mul_one, mul_zero]
  rw [sum_sub_distrib, mul_sub, prefixSum bl f, prefixSum al f]
  dsimp only [f]
  rw [doublePrefix, doublePrefix]
  dsimp only [a, b, residueError, phase]
  ring

theorem gapSort_cutMoment_exact {n h : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) :
    2 * cutMoment (gapSort p h) T =
      ∑ r : Fin h, ((h : ℤ) * residueError p h T r.val ^ 2 +
        phase h T r.val * residueError p h T r.val) := by
  unfold cutMoment
  rw [← (positionChainEquiv n h hh).symm.sum_comp, Fintype.sum_sigma, mul_sum]
  apply sum_congr rfl
  intro r _
  simp_rw [lower_at_coord p hh T, positionChainEquiv_symm_val, ideal_ord T _ hh r.isLt]
  push_cast
  exact coordMoment p T hT hh r

theorem gapSort_cutMoment_le {n h : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) :
    2 * cutMoment (gapSort p h) T ≤
      (h : ℤ) * ∑ r : Fin h, (residueError p h T r.val ^ 2 + |residueError p h T r.val|) := by
  rw [gapSort_cutMoment_exact p T hT hh, mul_sum]
  apply sum_le_sum
  intro r _
  rw [mul_add]
  apply add_le_add_right
  calc
    _ ≤ |phase h T r.val * residueError p h T r.val| := le_abs_self _
    _ = _ := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (phase_abs_le T hh r.isLt) (abs_nonneg _)

/-- Error of the current threshold at one physical slot. -/
def slotError {n : ℕ} (p : RankPlacement n) (T : ℕ) (i : Fin n) : ℤ :=
  (if i ∈ thresholdSet p T then 1 else 0) - (if i.val < T then 1 else 0)

theorem sum_slotError {n : ℕ} (p : RankPlacement n) (T : ℕ) :
    ∑ i, slotError p T i = 0 := by
  simp only [slotError, sum_sub_distrib, sub_eq_zero]
  rw [← Equiv.sum_comp p (fun i : Fin n => if i ∈ thresholdSet p T then (1 : ℤ) else 0)]
  simp [threshold_mem]

theorem cutMoment_eq_thresholdMoment {n : ℕ} (p : RankPlacement n) (t : ℕ) :
    cutMoment p (t + 1) = RoughGapScaleAssembly.thresholdMoment p t := by
  unfold cutMoment
  change (∑ i : Fin n, ((i.val : ℤ) - (t + 1 : ℕ)) * slotError p (t + 1) i) = _
  simp_rw [sub_mul]
  rw [sum_sub_distrib, ← mul_sum, sum_slotError, mul_zero, sub_zero]
  rw [← Equiv.sum_comp p (fun i : Fin n => (i.val : ℤ) * slotError p (t + 1) i)]
  simp only [slotError, threshold_mem, Equiv.symm_apply_apply, Nat.lt_succ_iff,
    RoughGapScaleAssembly.thresholdMoment]

private theorem idealFilterSum {n : ℕ} (h T r : ℕ) (hT : T ≤ n) :
    (∑ i : Fin n, if i.val % h = r then (if i.val < T then (1 : ℤ) else 0) else 0) =
      (residuePrefixCount h r T : ℤ) := by
  let f := fun v : ℕ => if v % h = r then (1 : ℤ) else 0
  calc
    _ = ∑ i : Fin n, if i.val < T then f i.val else 0 := by
      apply sum_congr rfl
      intro i _
      dsimp only [f]
      split_ifs <;> rfl
    _ = _ := by rw [prefixSum hT f]; simp [f, residuePrefixCount]

private theorem countFilterSum {n : ℕ} (B : Finset (Fin n)) (h r : ℕ) :
    (∑ i : Fin n, if i.val % h = r then (if i ∈ B then (1 : ℤ) else 0) else 0) =
      (chainLowerCount B h r : ℤ) := by
  classical
  unfold chainLowerCount
  have hf : B.filter (fun i => i.val % h = r) =
      univ.filter (fun i : Fin n => i.val % h = r ∧ i ∈ B) := by
    ext i
    simp [and_comm]
  rw [hf, ← sum_boole]
  apply sum_congr rfl
  intro i _
  by_cases hr : i.val % h = r <;> simp [hr]

theorem residueError_eq_sum {n h : ℕ} (p : RankPlacement n) (T r : ℕ) (hT : T ≤ n) :
    residueError p h T r = ∑ i : Fin n, if i.val % h = r then slotError p T i else 0 := by
  have split (P : Prop) [Decidable P] (a b : ℤ) :
      (if P then a - b else 0) = (if P then a else 0) - (if P then b else 0) := by
    by_cases P <;> simp [*]
  simp_rw [slotError, split]
  rw [sum_sub_distrib, countFilterSum, idealFilterSum _ _ _ hT]
  rfl

theorem sum_abs_residueError_le {n h : ℕ} (p : RankPlacement n) (T : ℕ) (hT : T ≤ n)
    (hh : 0 < h) :
    ∑ r : Fin h, |residueError p h T r.val| ≤ ∑ i, |slotError p T i| := by
  calc
    _ ≤ ∑ r : Fin h, ∑ i : Fin n, |if i.val % h = r.val then slotError p T i else 0| := by
      apply sum_le_sum
      intro r _
      rw [residueError_eq_sum p T r.val hT]
      exact abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      let r : Fin h := ⟨i.val % h, Nat.mod_lt _ hh⟩
      have he (z : Fin h) : i.val % h = z.val ↔ r = z := (Fin.ext_iff (a := r) (b := z)).symm
      simp [he, apply_ite abs]

private theorem prefixMass {L : ℕ} (a b : ℕ) (ha : a ≤ L) (hb : b ≤ L) :
    (∑ v : Fin L, |(if v.val < b then (1 : ℤ) else 0) - (if v.val < a then 1 else 0)|) =
      |(b : ℤ) - a| := by
  have sb := prefixSum hb (fun _ => (1 : ℤ))
  have sa := prefixSum ha (fun _ => (1 : ℤ))
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at sb sa
  by_cases cmp : a ≤ b
  · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (b : ℤ) - a)]
    have pos (v : Fin L) : (if v.val < a then (1 : ℤ) else 0) ≤
        (if v.val < b then 1 else 0) := by split_ifs <;> omega
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (pos _))]
    rw [sum_sub_distrib, sa, sb]
  · rw [abs_of_nonpos (by omega : (b : ℤ) - a ≤ 0)]
    have neg (v : Fin L) : (if v.val < b then (1 : ℤ) else 0) ≤
        (if v.val < a then 1 else 0) := by split_ifs <;> omega
    simp_rw [abs_of_nonpos (sub_nonpos.mpr (neg _)), neg_sub]
    rw [sum_sub_distrib, sa, sb]

theorem gapSort_abs_error_exact {n h : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) :
    ∑ i, |slotError (gapSort p h) T i| = ∑ r : Fin h, |residueError p h T r.val| := by
  unfold slotError
  rw [← (positionChainEquiv n h hh).symm.sum_comp, Fintype.sum_sigma]
  apply sum_congr rfl
  intro r _
  simp_rw [lower_at_coord p hh T, positionChainEquiv_symm_val, ideal_ord T _ hh r.isLt]
  apply prefixMass
  · rw [← actual_chain_length n h hh r, chainPositions_card]
    unfold residuePrefixCount
    exact sum_le_sum_of_subset_of_nonneg (range_mono hT) (by intros; positivity)
  · rw [← actual_chain_length n h hh r, chainPositions_card]
    exact chainLowerCount_le_length _ _ _

/-- Exact post-pass square displacement using the incoming threshold
residuals only. No randomness or large-sieve estimate is used. -/
theorem gapSort_squareDisplacement_exact {n h : ℕ} (p : RankPlacement n) (hh : 0 < h) :
    RoughGapScaleAssembly.squareDisplacement (gapSort p h) =
    ∑ t ∈ range n, ∑ r : Fin h,
      ((h : ℤ) * residueError p h (t + 1) r.val ^ 2 +
        phase h (t + 1) r.val * residueError p h (t + 1) r.val) := by
  rw [← RoughGapScaleAssembly.twice_sum_thresholdMoment, mul_sum]
  apply sum_congr rfl
  intro t ht
  rw [← cutMoment_eq_thresholdMoment, gapSort_cutMoment_exact p _ (mem_range.mp ht) hh]

theorem residueError_sum {n h : ℕ} (p : RankPlacement n) (T : ℕ) (hT : T ≤ n) (hh : 0 < h) :
    ∑ r : Fin h, residueError p h T r.val = 0 := by
  simp_rw [residueError_eq_sum p T _ hT]
  rw [sum_comm]
  apply Eq.trans _ (sum_slotError p T)
  apply sum_congr rfl
  intro i _
  let r : Fin h := ⟨i.val % h, Nat.mod_lt _ hh⟩
  have he (z : Fin h) : i.val % h = z.val ↔ r = z := (Fin.ext_iff (a := r) (b := z)).symm
  simp [he]

/-- The absolute phase remainder can be improved to h−1 using mass zero. -/
theorem gapSort_energy_remainder {n h : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) :
    |2 * cutMoment (gapSort p h) T -
      (h : ℤ) * ∑ r : Fin h, residueError p h T r.val ^ 2| ≤
    ((h : ℤ) - 1) * ∑ i, |slotError (gapSort p h) T i| := by
  rw [gapSort_abs_error_exact p T hT hh, gapSort_cutMoment_exact p T hT hh, sum_add_distrib,
    mul_sum, add_sub_cancel_left, mul_sum]
  have hs := residueError_sum p T hT hh
  have shift : (∑ r : Fin h, (phase h T r.val + 1) * residueError p h T r.val) =
      ∑ r : Fin h, phase h T r.val * residueError p h T r.val := by
    simp_rw [add_mul, one_mul]
    rw [sum_add_distrib, hs, add_zero]
  rw [← shift]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hb := counted_residual_bounds h r.val T hh r.isLt
  unfold phase
  apply abs_le.mpr
  omega










end Shellsort.RoughGapEndpoint

/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.ModEq

/-! Cutoff-ring interaction in physical residue coordinates. The inner input is
one bounded vector on a single interval; zeros model missing or truncated slots. -/

@[expose] public section

namespace Shellsort.RoughGapFarInteraction

open Finset

/-- The residue of a local interval slot after shifting by the interval start. -/
def intervalResidue {length gap : ℕ} (positive : 0 < gap) (start : ℕ)
    (i : Fin length) : Fin gap := ⟨(start + i.val) % gap, Nat.mod_lt _ positive⟩

theorem interval_capacity {length gap : ℕ} (positive : 0 < gap) (start : ℕ)
    (r : Fin gap) :
    ((univ : Finset (Fin length)).filter (fun i => intervalResidue positive start i = r)).card
      ≤ length / gap + 1 := by
  rw [← card_range (length / gap + 1)]
  apply card_le_card_of_injOn (fun i : Fin length => i.val / gap)
  · intro i _
    apply mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)
  · intro i hi j hj equalQuotient
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    have same : start + i.val ≡ start + j.val [MOD gap] :=
      congrArg Fin.val (hi'.trans hj'.symm)
    have rem : i.val % gap = j.val % gap := Nat.ModEq.add_left_cancel' start same
    change i.val / gap = j.val / gap at equalQuotient
    apply Fin.ext
    calc
      i.val = i.val % gap + gap * (i.val / gap) := (Nat.mod_add_div _ _).symm
      _ = j.val % gap + gap * (j.val / gap) := by rw [rem, equalQuotient]
      _ = j.val := Nat.mod_add_div _ _

/-- The sum of vector entries assigned to one residue. -/
def bucket {ι : Type*} [Fintype ι] {h : ℕ}
    (col : ι → Fin h) (v : ι → ℝ) (r : Fin h) : ℝ :=
  ∑ i : ι, if col i = r then v i else 0

/-- The residue sum minus the total vector mass divided by the number of residues. -/
noncomputable def centered {ι : Type*} [Fintype ι] {h : ℕ}
    (col : ι → Fin h) (v : ι → ℝ) (r : Fin h) : ℝ :=
  bucket col v r - (∑ i, v i) / h

private theorem centered_add {ι : Type*} [Fintype ι] {h : ℕ} (col : ι → Fin h)
    (u v : ι → ℝ) (r : Fin h) :
    centered col (fun i => u i + v i) r = centered col u r + centered col v r := by
  have raw : bucket col (fun i => u i + v i) r = bucket col u r + bucket col v r := by
    unfold bucket
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : col i = r <;> simp [hi]
  unfold centered
  rw [raw, sum_add_distrib, add_div]
  ring

private theorem centered_sum {ι κ : Type*} [Fintype ι] {h : ℕ} (col : ι → Fin h)
    (J : Finset κ) (u : κ → ι → ℝ) (r : Fin h) :
    centered col (fun i => ∑ k ∈ J, u k i) r = ∑ k ∈ J, centered col (u k) r := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [centered, bucket]
  | @insert k J hk ih => simp only [sum_insert hk, centered_add, ih]

/-- Folding the inner annuli before the estimate preserves their actual
centered cross term exactly, even when the individual annuli have nonzero mass. -/
theorem merge_inner_cross {ι κ : Type*} [Fintype ι] {h : ℕ}
    (col : ι → Fin h) (J : Finset κ) (u : κ → ι → ℝ) (outer : Fin h → ℝ) :
    (∑ k ∈ J, ∑ r, centered col (u k) r * outer r) =
      ∑ r, centered col (fun i => ∑ k ∈ J, u k i) r * outer r := by
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  rw [centered_sum, sum_mul]

/-- For an inner radius 2ʲ H and the m-separated outer annulus, its positions
have distance at least 2ʲ⁺ᵐ H / 2. -/
theorem dyadic_interval_separation (j m : ℕ) (H len distance : ℝ)
    (lengthBound : len ≤ 2 * (2 : ℝ) ^ j * H)
    (outerBound : (2 : ℝ) ^ (j + m) * H ≤ 2 * distance) :
    len ≤ 4 * (1 / (2 : ℝ) ^ m) * distance := by
  have positive : 0 < (2 : ℝ) ^ m := by positivity
  apply le_of_mul_le_mul_right (a := (2 : ℝ) ^ m) _ positive
  rw [pow_add] at outerBound
  calc
    _ ≤ (2 * (2 : ℝ) ^ j * H) * (2 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right lengthBound positive.le
    _ ≤ 4 * distance := by nlinarith
    _ = _ := by field_simp

private theorem bucket_total_abs {ι : Type*} [Fintype ι] {h : ℕ}
    (col : ι → Fin h) (v : ι → ℝ) :
    ∑ r, |bucket col v r| ≤ ∑ i, |v i| := by
  classical
  calc
    _ ≤ ∑ r : Fin h, ∑ i : ι, if col i = r then |v i| else 0 := by
      apply sum_le_sum
      intro r _
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i _
      by_cases hc : col i = r <;> simp [hc]
    _ = _ := by rw [sum_comm]; simp

theorem centered_total_abs {ι : Type*} [Fintype ι] {h : ℕ} (hh : 0 < h)
    (col : ι → Fin h) (v : ι → ℝ) :
    ∑ r, |centered col v r| ≤ 2 * ∑ i, |v i| := by
  have hr : (0 : ℝ) < h := by exact_mod_cast hh
  have normalized : (∑ _r : Fin h, |(∑ i : ι, v i) / (h : ℝ)|) = |∑ i : ι, v i| := by
    simp [abs_div, abs_of_nonneg hr.le]
    field_simp
  calc
    _ ≤ ∑ r : Fin h, (|bucket col v r| + |(∑ i : ι, v i) / (h : ℝ)|) :=
      sum_le_sum (fun _ _ => abs_sub ..)
    _ = (∑ r, |bucket col v r|) + |∑ i : ι, v i| := by rw [sum_add_distrib, normalized]
    _ ≤ (∑ i, |v i|) + ∑ i, |v i| := add_le_add (bucket_total_abs col v) (abs_sum_le_sum_abs _ _)
    _ = _ := by ring

theorem centered_interval_max {length h : ℕ} (hh : 0 < h) (start : ℕ)
    (v : Fin length → ℝ) (unit : ∀ i, |v i| ≤ 1) (r : Fin h) :
    (h : ℝ) * |centered (intervalResidue hh start) v r| ≤ h + 2 * (length : ℝ) := by
  classical
  have hr : (0 : ℝ) < h := by exact_mod_cast hh
  have vtotal : |∑ i, v i| ≤ (length : ℝ) := by
    calc
      _ ≤ ∑ i, |v i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin length, (1 : ℝ) := sum_le_sum (fun i _ => unit i)
      _ = _ := by simp
  have single : |bucket (intervalResidue hh start) v r| ≤ ((length / h : ℕ) : ℝ) + 1 := by
    unfold bucket
    rw [← sum_filter]
    calc
      _ ≤ ∑ i ∈ univ.filter (fun i : Fin length => intervalResidue hh start i = r), |v i| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ (univ : Finset (Fin length)).filter (fun i => intervalResidue hh start i = r),
            (1 : ℝ) := sum_le_sum (fun i _ => unit i)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast interval_capacity hh start r
  have divbound : (((length / h : ℕ) : ℝ) * h) ≤ length := by
    exact_mod_cast Nat.div_mul_le_self length h
  have mean : (h : ℝ) * |(∑ i, v i) / (h : ℝ)| = |∑ i, v i| := by
    rw [abs_div, abs_of_nonneg hr.le]; field_simp
  calc
    _ ≤ (h : ℝ) * (|bucket (intervalResidue hh start) v r| + |(∑ i, v i) / (h : ℝ)|) :=
      mul_le_mul_of_nonneg_left (abs_sub ..) hr.le
    _ = (h : ℝ) * |bucket (intervalResidue hh start) v r| + |∑ i, v i| := by rw [mul_add, mean]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left single hr.le]

/-- Both orders of the off-diagonal inner product against one outer annulus.
The arbitrary outer map can be the actual array's residue map. The inner
interval is allowed to have either sign and to extend past a truncated boundary
through zero-padding. -/
theorem far_inner_outer {ι : Type*} [Fintype ι] {length h : ℕ} (hh : 0 < h)
    (start : ℕ) (v : Fin length → ℝ) (unit : ∀ i, |v i| ≤ 1)
    (col : ι → Fin h) (w : ι → ℝ) :
    |2 * h * ∑ r, centered (intervalResidue hh start) v r * centered col w r| ≤
      (4 * h + 8 * length) * ∑ i, |w i| := by
  have hr : (0 : ℝ) < h := by exact_mod_cast hh
  let x := centered (intervalResidue hh start) v
  let y := centered col w
  have localBound (r : Fin h) : (h : ℝ) * |x r * y r| ≤ (h + 2 * (length : ℝ)) * |y r| := by
    rw [abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (centered_interval_max hh start v unit r) (abs_nonneg _)
  have step : (h : ℝ) * |∑ r, x r * y r| ≤ (h + 2 * (length : ℝ)) * ∑ r, |y r| := by
    calc
      _ ≤ (h : ℝ) * ∑ r, |x r * y r| := mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hr.le
      _ ≤ _ := by simpa only [mul_sum] using sum_le_sum (fun r _ => localBound r)
  have outer := centered_total_abs hh col w
  change (∑ r, |y r|) ≤ _ at outer
  have hc : (0 : ℝ) ≤ h + 2 * (length : ℝ) := by positivity
  have finalBound := step.trans (mul_le_mul_of_nonneg_left outer hc)
  change |2 * (h : ℝ) * ∑ r, x r * y r| ≤ _
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * h)]
  nlinarith

/-- Sum over the outer rings. The geometric condition says that, wherever an
outer vector is nonzero, its associated combined inner interval has length at
most 4 ρ distance. For dyadic m-separated rings, take ρ = 2⁻ᵐ. -/
theorem sum_far_interactions {ι κ : Type*} [Fintype ι] [Fintype κ]
    {h : ℕ} (hh : 0 < h) (H ρ : ℝ) (gapBound : (h : ℝ) ≤ 2 * H)
    (length start : κ → ℕ) (v : (k : κ) → Fin (length k) → ℝ)
    (unit : ∀ k i, |v k i| ≤ 1) (col : ι → Fin h) (w : κ → ι → ℝ)
    (distance : ι → ℝ)
    (separation : ∀ k i, w k i ≠ 0 → (length k : ℝ) ≤ 4 * ρ * distance i) :
    (∑ k, |2 * h * ∑ r, centered (intervalResidue hh (start k)) (v k) r *
      centered col (w k) r|) ≤
      ∑ k, ∑ i, (8 * H + 32 * ρ * distance i) * |w k i| := by
  apply sum_le_sum
  intro k _
  apply (far_inner_outer hh (start k) (v k) (unit k) col (w k)).trans
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  by_cases zero : w k i = 0
  · simp [zero]
  · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    linarith [separation k i zero]








end Shellsort.RoughGapFarInteraction

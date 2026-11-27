/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Embedding
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Lifting approximants: the telescoping argument

Let `ι : Y → X` be a bounded linear map and `A` a scheme in `X`.  A **lifting bound** of
exponent `β` says that every approximant is the image of an element of `Y` of controlled size:

`a ∈ A n, n ≥ 1  ⟹  a = ι y  with  ‖y‖_Y ≤ C n^β ‖a‖_X`   (`ApproximationScheme.LiftBound`).

For `Y` a space of smooth functions this is **Bernstein's inequality** (`β` the smoothness);
for `Y = L_r ⊆ X = L_p` it is **Nikolskii's inequality** (`β = d (1/p - 1/r)`).

Given `f ∈ X`, choose near-best approximants `a_k ∈ A (2^k)` (`DyadicApprox`), so that
`f = a_0 + ∑_k (a_{k+1} - a_k)` with blocks `a_{k+1} - a_k ∈ A (2^(k+2))` of size
`≲ E_{2^k}(f)`.  Lift every block to `Y`: the lifted blocks have size `≲ 2^(kβ) E_{2^k}(f)`, so
if `∑_k 2^(kβ) E_{2^k}(f) < ∞` their series converges in the Banach space `Y` to some `y` with
`ι y = f` (`DyadicApprox.exists_preimage`).  The partial sums of that series lift the
approximants `a_k`, and the tails bound how well `y` is approximated in `Y`.

This single construction yields three theorems: Bernstein implies `A^β_1 ↪ Y`
(`exists_preimage_of_liftBound`, this file), the Nikolskii transfer theorem
(`ApproximationSpaces.Nikolskii`), and one half of the representation theorem.  The
approximants themselves are controlled in `X` and in `A^r_∞` (`DyadicApprox.enorm_le`,
`DyadicApprox.approxNormDyadic_top_le`).

**Tolerances.** Best approximants need not exist, so `a_k` is only near-best:
`‖f - a_k‖ ≤ E_{2^k}(f) + t_k`.  The tolerances `t_k = ‖f‖ 2^(-k(σ+1))` are chosen so small
that every weighted sum of them that occurs is at most `2 ‖f‖`, which is absorbed into the
final constant; this avoids a limit `ε → 0`.  The resulting bounds of the tolerances against
the errors (`tsum_dyadicWeight_mul_add_tolerance_le`, `mul_add_mul_tsum_tolerance_le`,
`lqNorm_approxSeqDyadic_add_tolerance_le`) serve every theorem built on the construction.
The tails of the lifted series are bounded by the tail of a convergent series,
`‖f - ∑_{i<n} a_i‖ ≤ ∑_{i ≥ 0} ‖a_{i+n}‖` (`HasSum.enorm_sub_sum_range_le`).
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

/-- **The tail of a convergent series**: if `∑_i a_i = f`, then
`‖f - ∑_{i<n} a_i‖ ≤ ∑_{i ≥ 0} ‖a_{i+n}‖`. -/
theorem HasSum.enorm_sub_sum_range_le {E : Type*} [NormedAddCommGroup E] {a : ℕ → E} {f : E}
    (h : HasSum a f) (n : ℕ) : ‖f - ∑ i ∈ range n, a i‖ₑ ≤ ∑' i, ‖a (i + n)‖ₑ := by
  rw [← h.tsum_eq, ← ((summable_nat_add_iff n).2 h.summable).sum_add_tsum_nat_add',
    add_sub_cancel_left]
  exact eNorm_tsum_le_tsum_eNorm

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A **lifting bound** of exponent `β` and constant `C` for `ι : Y → X`: every approximant
`a ∈ A n`, `n ≥ 1`, is `ι y` for some `y` with `‖y‖ ≤ C n^β ‖a‖`.  This is Bernstein's
inequality when `Y` is a smoothness space and Nikolskii's inequality when `Y ⊆ X` is a
smaller Lebesgue space. -/
def LiftBound (ι : Y →L[ℝ] X) (A : ApproximationScheme X) (β C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ a ∈ A n, ∃ y : Y, ι y = a ∧ ‖y‖ ≤ C * (n : ℝ) ^ β * ‖a‖

variable {ι : Y →L[ℝ] X} {A : ApproximationScheme X} {β C : ℝ}

/-- The lifting bound in `ℝ≥0∞`. -/
theorem LiftBound.exists_enorm_le (hB : LiftBound ι A β C) (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n)
    {a : X} (ha : a ∈ A n) :
    ∃ y : Y, ι y = a ∧ ‖y‖ₑ ≤ ENNReal.ofReal C * (n : ℝ≥0∞) ^ β * ‖a‖ₑ := by
  obtain ⟨y, hy, hle⟩ := hB n hn a ha
  refine ⟨y, hy, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos hn0,
    ← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hle

/-- The constant `2 C 4^β` by which a lifted dyadic block exceeds `2^(kβ)` times its error. -/
noncomputable def liftConst (C β : ℝ) : ℝ≥0∞ := 2 * ENNReal.ofReal C * dyadicWeight β 2

/-- The lifting constant is finite. -/
theorem liftConst_ne_top (C β : ℝ) : liftConst C β ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (ENNReal.dyadicWeight_ne_top β 2)

/-- A **dyadic sequence of near-best approximants** of `f` with tolerances `t`:
`a k ∈ A (2^k)` and `‖f - a k‖ ≤ E_{2^k}(f) + t k`. -/
structure DyadicApprox (A : ApproximationScheme X) (f : X) (t : ℕ → ℝ≥0∞) where
  /-- The approximant of complexity `2^k`. -/
  a : ℕ → X
  /-- The approximant `a k` lies in `A (2^k)`. -/
  mem : ∀ k, a k ∈ A (2 ^ k)
  /-- `a k` is near-best: `‖f - a k‖ ≤ E_{2^k}(f) + t k`. -/
  eNorm_sub_le : ∀ k, ‖f - a k‖ₑ ≤ A.approxError f (2 ^ k) + t k

/-- Near-best approximants exist for every choice of positive tolerances. -/
theorem exists_dyadicApprox (A : ApproximationScheme X) (f : X) {t : ℕ → ℝ≥0∞}
    (ht0 : ∀ k, t k ≠ 0) : Nonempty (A.DyadicApprox f t) := by
  choose a ha h using fun k => exists_mem_enorm_sub_le_add (A := A) (2 ^ k) f (ht0 k)
  exact ⟨⟨a, ha, h⟩⟩

namespace DyadicApprox

variable {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t)

/-- Consecutive approximants differ by an approximant of complexity `2^(k+2)`. -/
theorem sub_mem (k : ℕ) : D.a (k + 1) - D.a k ∈ A (2 ^ (k + 2)) :=
  sub_mem_pow_add_two (D.mem (k + 1)) (D.mem k)

/-- The blocks are controlled by the errors: `‖a_{k+1} - a_k‖ ≤ 2 (E_{2^k}(f) + t_k)`. -/
theorem enorm_sub_succ_le (ht : Antitone t) (k : ℕ) :
    ‖D.a (k + 1) - D.a k‖ₑ ≤ 2 * (A.approxError f (2 ^ k) + t k) := by
  calc ‖D.a (k + 1) - D.a k‖ₑ = ‖(f - D.a k) - (f - D.a (k + 1))‖ₑ := by congr 1; abel
    _ ≤ ‖f - D.a k‖ₑ + ‖f - D.a (k + 1)‖ₑ := _root_.eNorm_sub_le
    _ ≤ (A.approxError f (2 ^ k) + t k) + (A.approxError f (2 ^ (k + 1)) + t (k + 1)) :=
        add_le_add (D.eNorm_sub_le k) (D.eNorm_sub_le (k + 1))
    _ ≤ (A.approxError f (2 ^ k) + t k) + (A.approxError f (2 ^ k) + t k) := by
        gcongr
        · exact approxError_anti f (Nat.pow_le_pow_right two_pos (Nat.le_succ k))
        · exact ht (Nat.le_succ k)
    _ = 2 * (A.approxError f (2 ^ k) + t k) := by ring

/-- A near-best approximant of complexity `2^k` has norm at most `2 ‖f‖ + t_k`. -/
theorem enorm_le (k : ℕ) : ‖D.a k‖ₑ ≤ 2 * ‖f‖ₑ + t k :=
  calc ‖D.a k‖ₑ = ‖f - (f - D.a k)‖ₑ := by rw [sub_sub_cancel]
    _ ≤ ‖f‖ₑ + ‖f - D.a k‖ₑ := _root_.eNorm_sub_le
    _ ≤ ‖f‖ₑ + (‖f‖ₑ + t k) := by
        gcongr
        exact (D.eNorm_sub_le k).trans (by gcongr; exact approxError_le_enorm f _)
    _ = 2 * ‖f‖ₑ + t k := by ring

/-- The first approximant is bounded: `‖a_0‖ ≤ 2 ‖f‖ + t_0`. -/
theorem enorm_zero_le : ‖D.a 0‖ₑ ≤ 2 * ‖f‖ₑ + t 0 := D.enorm_le 0

/-- **The errors of a near-best approximant**: for decreasing tolerances and `j ≤ k`,
`E_{2^j}(a_k) ≤ E_{2^j}(f) + ‖f - a_k‖ ≤ 2 (E_{2^j}(f) + t_j)`. -/
theorem approxError_le (ht : Antitone t) {j k : ℕ} (hjk : j ≤ k) :
    A.approxError (D.a k) (2 ^ j) ≤ 2 * (A.approxError f (2 ^ j) + t j) :=
  calc A.approxError (D.a k) (2 ^ j) ≤ A.approxError f (2 ^ j) + ‖D.a k - f‖ₑ :=
        approxError_le_approxError_add_enorm _ _ _
    _ ≤ A.approxError f (2 ^ j) + (A.approxError f (2 ^ j) + t j) := by
        rw [eNorm_sub_rev]
        gcongr
        exact (D.eNorm_sub_le k).trans
          (add_le_add (approxError_anti f (Nat.pow_le_pow_right two_pos hjk)) (ht hjk))
    _ ≤ 2 * (A.approxError f (2 ^ j) + t j) := by
        rw [two_mul]
        gcongr
        exact le_self_add

/-- **The quasi-norm of `A^r_∞` of a near-best approximant**: for decreasing tolerances with
`t_0 ≤ ‖f‖`, `‖a_k‖_{A^r_∞} ≤ 3 ‖f‖ + 2 ∑_{j ≤ k} 2^(jr) (E_{2^j}(f) + t_j)`. -/
theorem approxNormDyadic_top_le {r : ℝ} (ht : Antitone t) (ht0 : t 0 ≤ ‖f‖ₑ) (k : ℕ) :
    A.approxNormDyadic r ∞ (D.a k) ≤ 3 * ‖f‖ₑ +
      2 * ∑ j ∈ range (k + 1), dyadicWeight r j * (A.approxError f (2 ^ j) + t j) := by
  refine (approxNormDyadic_top_le_of_mem (D.mem k)).trans (add_le_add ?_ ?_)
  · calc ‖D.a k‖ₑ ≤ 2 * ‖f‖ₑ + t k := D.enorm_le k
      _ ≤ 2 * ‖f‖ₑ + ‖f‖ₑ := by gcongr; exact (ht (Nat.zero_le k)).trans ht0
      _ = 3 * ‖f‖ₑ := by ring
  · rw [Finset.mul_sum]
    calc ∑ j ∈ range k, A.approxSeqDyadic r (D.a k) j
        ≤ ∑ j ∈ range k, 2 * (dyadicWeight r j * (A.approxError f (2 ^ j) + t j)) :=
          sum_le_sum fun j hj => by
            rw [approxSeqDyadic, mul_left_comm]
            gcongr
            exact D.approxError_le ht (mem_range.1 hj).le
      _ ≤ _ := sum_le_sum_of_subset (range_mono (Nat.le_succ k))

/-- The approximants converge to `f` when the dyadic errors and the tolerances tend to `0`. -/
theorem tendsto (he : Tendsto (fun k => A.approxError f (2 ^ k)) atTop (𝓝 0))
    (ht : Tendsto t atTop (𝓝 0)) : Tendsto D.a atTop (𝓝 f) := by
  have h : Tendsto (fun k => ‖f - D.a k‖ₑ) atTop (𝓝 0) := by
    have := he.add ht
    rw [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
      D.eNorm_sub_le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def, norm_sub_rev] using this

/-- **Lifting the blocks**: `a_0 = ι y_0` and `a_{k+1} - a_k = ι d_k` with
`‖y_0‖ ≤ C ‖a_0‖` and `‖d_k‖ ≤ C 2^((k+2)β) ‖a_{k+1} - a_k‖`. -/
theorem exists_lift (hB : LiftBound ι A β C) (hC : 0 ≤ C) :
    ∃ y0 : Y, ∃ d : ℕ → Y, ι y0 = D.a 0 ∧ (∀ k, ι (d k) = D.a (k + 1) - D.a k) ∧
      ‖y0‖ₑ ≤ ENNReal.ofReal C * ‖D.a 0‖ₑ ∧
      ∀ k, ‖d k‖ₑ ≤ ENNReal.ofReal C * dyadicWeight β (k + 2) * ‖D.a (k + 1) - D.a k‖ₑ := by
  obtain ⟨y0, hy0, hy0le⟩ := hB.exists_enorm_le hC (n := 2 ^ 0) le_rfl (D.mem 0)
  have : ∀ k, ∃ z : Y, ι z = D.a (k + 1) - D.a k ∧
      ‖z‖ₑ ≤ ENNReal.ofReal C * ((2 ^ (k + 2) : ℕ) : ℝ≥0∞) ^ β * ‖D.a (k + 1) - D.a k‖ₑ :=
    fun k => hB.exists_enorm_le hC Nat.one_le_two_pow (D.sub_mem k)
  choose d hd hdle using this
  refine ⟨y0, d, hy0, hd, by simpa using hy0le, fun k => ?_⟩
  rw [← ENNReal.natCast_two_pow_rpow]
  exact hdle k

include D in
/-- **The lifted partial sums.**  There are `y_0` and `d_k` in `Y` whose partial sums
`z_n = y_0 + ∑_{j<n} d_j` lift the approximants, `ι z_n = a_n`, with
`‖y_0‖ ≤ C (2 ‖f‖ + t_0)` and `‖d_k‖ ≤ K 2^(kβ) (E_{2^k}(f) + t_k)`, `K = liftConst C β`.
No completeness of `Y` is needed. -/
theorem exists_lift_partial (ht : Antitone t) (hB : LiftBound ι A β C) (hC : 0 ≤ C) :
    ∃ y0 : Y, ∃ d : ℕ → Y, (∀ n, ι (y0 + ∑ j ∈ range n, d j) = D.a n) ∧
      ‖y0‖ₑ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + t 0) ∧
      ∀ k, ‖d k‖ₑ ≤ liftConst C β * (dyadicWeight β k * (A.approxError f (2 ^ k) + t k)) := by
  obtain ⟨y0, d, hy0, hd, hy0le, hdle⟩ := D.exists_lift hB hC
  refine ⟨y0, d, fun n => ?_, hy0le.trans (by gcongr; exact D.enorm_zero_le), fun k => ?_⟩
  · rw [map_add, map_sum, hy0]
    simp_rw [hd]
    rw [Finset.sum_range_sub (fun k => D.a k) n]
    abel
  · calc ‖d k‖ₑ ≤ ENNReal.ofReal C * dyadicWeight β (k + 2) * ‖D.a (k + 1) - D.a k‖ₑ := hdle k
      _ ≤ ENNReal.ofReal C * dyadicWeight β (k + 2) * (2 * (A.approxError f (2 ^ k) + t k)) := by
          gcongr; exact D.enorm_sub_succ_le ht k
      _ = _ := by simp only [liftConst, ENNReal.dyadicWeight_add_nat]; ring

include D in
/-- **The telescoping lift.**  If `∑_k 2^(kβ) (E_{2^k}(f) + t_k) < ∞`, then `f = ι y` for some
`y ∈ Y` with

* `‖y‖ ≤ C (2 ‖f‖ + t_0) + K ∑_k 2^(kβ) (E_{2^k}(f) + t_k)`, and
* for every `k` some `z` with `ι z ∈ A (2^k)` and
  `‖y - z‖ ≤ K ∑_{i ≥ 0} 2^((k+i)β) (E_{2^(k+i)}(f) + t_{k+i})`,

where `K = liftConst C β`. -/
theorem exists_preimage [CompleteSpace Y] (ht : Antitone t) (hB : LiftBound ι A β C)
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hsum : ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + t k) ≠ ∞) :
    ∃ y : Y, ι y = f ∧
      ‖y‖ₑ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + t 0) +
        liftConst C β * ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + t k) ∧
      ∀ k, ∃ z : Y, ι z ∈ A (2 ^ k) ∧
        ‖y - z‖ₑ ≤ liftConst C β *
          ∑' i, dyadicWeight β (k + i) * (A.approxError f (2 ^ (k + i)) + t (k + i)) := by
  obtain ⟨y0, d, hpart, hy0le, hdk⟩ := D.exists_lift_partial ht hB hC
  set g : ℕ → ℝ≥0∞ := fun k => dyadicWeight β k * (A.approxError f (2 ^ k) + t k)
  have hsumd : ∑' k, ‖d k‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (liftConst_ne_top C β) hsum)
      ((tsum_le_tsum hdk).trans_eq ENNReal.tsum_mul_left)
  have hsd : Summable d := Summable.of_eNorm hsumd
  -- the errors and the tolerances tend to zero
  have hg : Tendsto g atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hle1 : ∀ k, A.approxError f (2 ^ k) + t k ≤ g k := fun k =>
    le_mul_of_one_le_left' (ENNReal.one_le_dyadicWeight hβ k)
  have he : Tendsto (fun k => A.approxError f (2 ^ k)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun _ => bot_le)
      fun k => le_self_add.trans (hle1 k)
  have ht0 : Tendsto t atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun _ => bot_le)
      fun k => le_add_self.trans (hle1 k)
  set y := y0 + ∑' k, d k
  have hlim : Tendsto (fun n => ι (y0 + ∑ j ∈ range n, d j)) atTop (𝓝 (ι y)) :=
    (ι.continuous.tendsto y).comp (tendsto_const_nhds.add hsd.hasSum.tendsto_sum_nat)
  simp_rw [hpart] at hlim
  have hy : ι y = f := tendsto_nhds_unique hlim (D.tendsto he ht0)
  refine ⟨y, hy, ?_, fun k => ⟨y0 + ∑ j ∈ range k, d j, by rw [hpart]; exact D.mem k, ?_⟩⟩
  · calc ‖y‖ₑ ≤ ‖y0‖ₑ + ‖∑' k, d k‖ₑ := eNorm_add_le _ _
      _ ≤ ENNReal.ofReal C * (2 * ‖f‖ₑ + t 0) + ∑' k, liftConst C β * g k := by
          gcongr
          exact eNorm_tsum_le_tsum_eNorm.trans (tsum_le_tsum hdk)
      _ = _ := by rw [ENNReal.tsum_mul_left]
  · rw [show y = y0 + ∑' k, d k from rfl, add_sub_add_left_eq_sub]
    calc ‖∑' j, d j - ∑ j ∈ range k, d j‖ₑ ≤ ∑' i, ‖d (i + k)‖ₑ :=
          hsd.hasSum.enorm_sub_sum_range_le k
      _ ≤ ∑' i, liftConst C β * g (k + i) := tsum_le_tsum fun i => by
          rw [add_comm k i]; exact hdk (i + k)
      _ = _ := ENNReal.tsum_mul_left

end DyadicApprox

section Tolerance

variable {E : Type*} [NormedAddCommGroup E]

/-- The tolerances `t_k = ‖f‖ 2^(-k(σ+1))`: positive and finite for `f ≠ 0`, decreasing for
`σ ≥ -1`, and small against every weight `2^(kτ)` with `τ ≤ σ`. -/
noncomputable def tolerance (f : E) (σ : ℝ) (k : ℕ) : ℝ≥0∞ := ‖f‖ₑ * dyadicWeight (-(σ + 1)) k

/-- For `f ≠ 0` the tolerances are positive. -/
theorem tolerance_ne_zero {f : E} (hf : f ≠ 0) (σ : ℝ) (k : ℕ) : tolerance f σ k ≠ 0 :=
  mul_ne_zero (eNorm_ne_zero.2 hf) (ENNReal.dyadicWeight_ne_zero _ k)

/-- The tolerances are finite. -/
theorem tolerance_ne_top (f : E) (σ : ℝ) (k : ℕ) : tolerance f σ k ≠ ∞ :=
  ENNReal.mul_ne_top eNorm_ne_top (ENNReal.dyadicWeight_ne_top _ k)

/-- For `σ ≥ 0` the tolerances decrease. -/
theorem tolerance_anti (f : E) {σ : ℝ} (hσ : 0 ≤ σ) : Antitone (tolerance f σ) := fun _ _ h => by
  unfold tolerance
  gcongr
  exact ENNReal.dyadicWeight_anti (by linarith) h

/-- The first tolerance is `‖f‖`. -/
@[simp]
theorem tolerance_zero (f : E) (σ : ℝ) : tolerance f σ 0 = ‖f‖ₑ := by simp [tolerance]

/-- `2^(kτ) t_k ≤ ‖f‖ 2^(-k)` for `τ ≤ σ`. -/
theorem dyadicWeight_mul_tolerance_le (f : E) {σ τ : ℝ} (h : τ ≤ σ) (k : ℕ) :
    dyadicWeight τ k * tolerance f σ k ≤ ‖f‖ₑ * dyadicWeight (-1) k := by
  rw [tolerance, mul_left_comm, ← ENNReal.dyadicWeight_add]
  gcongr
  exact ENNReal.dyadicWeight_le_of_le (by linarith) k

/-- For `τ ≤ σ`, `∑_k 2^(kτ) ‖f‖ 2^(-k(σ+1)) ≤ 2 ‖f‖`. -/
theorem tsum_dyadicWeight_mul_tolerance_le (f : E) {σ τ : ℝ} (h : τ ≤ σ) :
    ∑' k, dyadicWeight τ k * tolerance f σ k ≤ 2 * ‖f‖ₑ := by
  calc ∑' k, dyadicWeight τ k * tolerance f σ k ≤ ∑' k, ‖f‖ₑ * dyadicWeight (-1) k :=
        tsum_le_tsum fun k => dyadicWeight_mul_tolerance_le f h k
    _ = 2 * ‖f‖ₑ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg_one, mul_comm]

/-- For `σ > -1` the tolerances tend to `0`. -/
theorem tendsto_tolerance (f : E) {σ : ℝ} (hσ : -1 < σ) :
    Tendsto (tolerance f σ) atTop (𝓝 0) := by
  have hr : (2 : ℝ≥0∞) ^ (-(σ + 1)) < 1 := ENNReal.two_rpow_neg_lt_one (by linarith)
  have hgeo := ENNReal.Tendsto.const_mul (a := ‖f‖ₑ)
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr eNorm_ne_top)
  rw [mul_zero] at hgeo
  refine hgeo.congr fun k => ?_
  rw [tolerance, ENNReal.dyadicWeight_eq_pow]

/-- For `σ ≥ 0`, `∑_k ‖f‖ 2^(-k(σ+1)) ≤ 2 ‖f‖`. -/
theorem tsum_tolerance_le (f : E) {σ : ℝ} (hσ : 0 ≤ σ) : ∑' k, tolerance f σ k ≤ 2 * ‖f‖ₑ := by
  have := tsum_dyadicWeight_mul_tolerance_le (σ := σ) (τ := 0) f hσ
  simp only [ENNReal.dyadicWeight_zero_left, one_mul] at this
  exact this

/-- For `τ ≤ σ`, `‖(2^(kτ) ‖f‖ 2^(-k(σ+1)))_k‖_{ℓ_q} ≤ 2 ‖f‖`. -/
theorem lqNorm_dyadicWeight_mul_tolerance_le {q : ℝ≥0∞} (hq : 1 ≤ q) (f : E) {σ τ : ℝ}
    (h : τ ≤ σ) : lqNorm q (fun k => dyadicWeight τ k * tolerance f σ k) ≤ 2 * ‖f‖ₑ := by
  calc lqNorm q (fun k => dyadicWeight τ k * tolerance f σ k)
      ≤ lqNorm q (fun k => ‖f‖ₑ * dyadicWeight (-1) k) :=
        ENNReal.lqNorm_mono fun k => dyadicWeight_mul_tolerance_le f h k
    _ = ‖f‖ₑ * lqNorm q (dyadicWeight (-1)) := ENNReal.lqNorm_const_mul _ _
    _ ≤ ‖f‖ₑ * 2 := by gcongr; exact ENNReal.lqNorm_dyadicWeight_neg_one_le hq
    _ = 2 * ‖f‖ₑ := mul_comm _ _

end Tolerance

/-! ### The tolerances against the errors -/

/-- **Splitting off the tolerances**: for `τ ≤ σ`,
`∑_k 2^(kτ) (E_{2^k}(f) + t_k) ≤ ‖(2^(kτ) E_{2^k}(f))_k‖_{ℓ_1} + 2 ‖f‖`, with the tolerances
`t_k = tolerance f σ k`. -/
theorem tsum_dyadicWeight_mul_add_tolerance_le (f : X) {σ τ : ℝ} (h : τ ≤ σ) :
    ∑' k, dyadicWeight τ k * (A.approxError f (2 ^ k) + tolerance f σ k) ≤
      lqNorm 1 (A.approxSeqDyadic τ f) + 2 * ‖f‖ₑ := by
  simp_rw [mul_add]
  rw [tsum_add, ← ENNReal.lqNorm_one]
  exact add_le_add le_rfl (tsum_dyadicWeight_mul_tolerance_le f h)

/-- For `τ ≤ σ` and `‖(2^(kτ) E_{2^k}(f))_k‖_{ℓ_1} < ∞`, the series
`∑_k 2^(kτ) (E_{2^k}(f) + t_k)` with the tolerances `t_k = tolerance f σ k` is finite. -/
theorem tsum_dyadicWeight_mul_add_tolerance_ne_top {f : X} {σ τ : ℝ} (h : τ ≤ σ)
    (hf : lqNorm 1 (A.approxSeqDyadic τ f) ≠ ∞) :
    ∑' k, dyadicWeight τ k * (A.approxError f (2 ^ k) + tolerance f σ k) ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, ENNReal.mul_ne_top (by norm_num) eNorm_ne_top⟩)
    (tsum_dyadicWeight_mul_add_tolerance_le f h)

/-- **The bound of a telescoping lift by the norm of `A^σ_1`**:
`c (2 ‖f‖ + ‖f‖) + K ∑_k 2^(kσ) (E_{2^k}(f) + t_k) ≤ (3 c + 3 K) ‖f‖_{A^σ_1}` with the
tolerances `t_k = tolerance f σ k`, for all `c, K ∈ [0, ∞]`. -/
theorem mul_add_mul_tsum_tolerance_le (c K : ℝ≥0∞) (f : X) (σ : ℝ) :
    c * (2 * ‖f‖ₑ + ‖f‖ₑ) +
        K * ∑' k, dyadicWeight σ k * (A.approxError f (2 ^ k) + tolerance f σ k) ≤
      (3 * c + 3 * K) * A.approxNormDyadic σ 1 f := by
  set L := lqNorm 1 (A.approxSeqDyadic σ f)
  have hN : A.approxNormDyadic σ 1 f = ‖f‖ₑ + L := rfl
  calc _ ≤ c * (3 * (‖f‖ₑ + L)) + K * (3 * (‖f‖ₑ + L)) := by
        gcongr
        · calc 2 * ‖f‖ₑ + ‖f‖ₑ = 3 * ‖f‖ₑ := by ring
            _ ≤ 3 * (‖f‖ₑ + L) := by gcongr; exact le_self_add
        · calc _ ≤ L + 2 * ‖f‖ₑ := tsum_dyadicWeight_mul_add_tolerance_le f le_rfl
            _ ≤ (‖f‖ₑ + L) + 2 * (‖f‖ₑ + L) := by gcongr; exacts [le_add_self, le_self_add]
            _ = 3 * (‖f‖ₑ + L) := by ring
    _ = _ := by rw [hN]; ring

/-- **The `ℓ_q` norm of the errors plus the tolerances**: for `q ≥ 1`,
`‖(2^(ks) E_{2^k}(f) + 2^(ks) t_k)_k‖_{ℓ_q} ≤ ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q} + 2 ‖f‖`, with the
tolerances `t_k = tolerance f s k`. -/
theorem lqNorm_approxSeqDyadic_add_tolerance_le {q : ℝ≥0∞} (hq : 1 ≤ q) (f : X) (s : ℝ) :
    lqNorm q (fun k => A.approxSeqDyadic s f k + dyadicWeight s k * tolerance f s k) ≤
      lqNorm q (A.approxSeqDyadic s f) + 2 * ‖f‖ₑ :=
  (ENNReal.lqNorm_add_le hq _ _).trans
    (add_le_add le_rfl (lqNorm_dyadicWeight_mul_tolerance_le hq f le_rfl))

/-- **A lifting bound of exponent `β` gives `A^β_1 ↪ Y`**: if
`∑_k 2^(kβ) E_{2^k}(f) < ∞`, then `f = ι y` with
`‖y‖ ≤ (3 C + 3 K) (‖f‖ + ∑_k 2^(kβ) E_{2^k}(f))`, `K = liftConst C β`.  For a Bernstein
inequality this is the embedding of the approximation space into the smoothness space. -/
theorem exists_preimage_of_liftBound [CompleteSpace Y] (hB : LiftBound ι A β C) (hC : 0 ≤ C)
    (hβ : 0 ≤ β) {f : X} (hf : lqNorm 1 (A.approxSeqDyadic β f) < ∞) :
    ∃ y : Y, ι y = f ∧
      ‖y‖ₑ ≤ (3 * ENNReal.ofReal C + 3 * liftConst C β) * A.approxNormDyadic β 1 f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero ι, by simp⟩
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 β)
  obtain ⟨y, hy, hyle, -⟩ := D.exists_preimage (tolerance_anti f hβ) hB hC hβ
    (tsum_dyadicWeight_mul_add_tolerance_ne_top le_rfl hf.ne)
  rw [tolerance_zero] at hyle
  exact ⟨y, hy, hyle.trans (mul_add_mul_tsum_tolerance_le _ _ f β)⟩

end ApproximationScheme

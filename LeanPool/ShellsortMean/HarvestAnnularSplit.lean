/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestMenuSieve
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Near and far ring terms. The inner rings of each far interaction
are summed with their signs intact. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestAnnularSplit
open Finset
open RoughGapDenominatorAverage

/-- Real part of the complex inner product. -/
def dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im

private theorem dot_sum {ι} (s : Finset ι) (x : ℂ) (v : ι → ℂ) :
    dot x (∑ i ∈ s, v i) = ∑ i ∈ s, dot x (v i) := by
  simp only [dot, Complex.re_sum, Complex.im_sum, mul_sum, sum_add_distrib]

private theorem twice_dot_le (x y : ℂ) : 2 * dot x y ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [dot, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]

private theorem update (x y : ℂ) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2+‖y‖ ^ 2 + 2 * dot y x := by
  simp only [dot, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

private theorem triangular (K : ℕ) (v : ℕ → ℂ) :
    ‖∑ k ∈ range K, v k‖ ^ 2 =
    ∑ k ∈ range K, (‖v k‖ ^ 2 + 2 * dot (v k) (∑ l ∈ range k, v l)) := by
  induction K with
  | zero => simp
  | succ k ih => rw [sum_range_succ, update, ih, sum_range_succ (f := fun j=>‖v j‖ ^ 2 + _)]; ring

def prev (K m k : ℕ) := (range K).filter (fun l => l < k ∧ k < l + m)

private theorem prev_card (K m k : ℕ) (hm : 0 < m) : (prev K m k).card ≤ m - 1 := by
  have sub : prev K m k ⊆ Ico (k + 1 - m) k := by
    intro l h
    obtain ⟨_, hl, hk⟩ := mem_filter.mp h
    exact mem_Ico.mpr ⟨by omega, hl⟩
  have hc := card_le_card sub
  rw [Nat.card_Ico] at hc
  omega

private theorem next_card (K m l : ℕ) (hm : 0 < m) :
    ((range K).filter (fun k => l < k ∧ k < l + m)).card ≤ m - 1 := by
  have sub : ((range K).filter (fun k => l < k ∧ k < l + m)) ⊆ Ico (l + 1) (l + m) := by
    intro k h
    obtain ⟨_, hl, hk⟩ := mem_filter.mp h
    exact mem_Ico.mpr ⟨by omega, hk⟩
  have hc := card_le_card sub
  rw [Nat.card_Ico] at hc
  omega

private theorem near_charge (K m : ℕ) (hm : 0 < m) (v : ℕ → ℂ) :
    (∑ k ∈ range K, ∑ l ∈ prev K m k, 2 * dot (v k) (v l)) ≤
    2 * ((m - 1 : ℕ) : ℝ) * ∑ k ∈ range K, ‖v k‖ ^ 2 := by
  let w := fun k => ‖v k‖ ^ 2
  have row : ∀ k, (∑ _l ∈ prev K m k, w k) ≤ ((m - 1 : ℕ) : ℝ) * w k := by
    intro k
    rw [sum_const, nsmul_eq_mul]
    gcongr
    exact_mod_cast prev_card K m k hm
  have col : ∀ l, (∑ _k ∈ (range K).filter (fun k => l < k ∧ k < l + m), w l) ≤
      ((m - 1 : ℕ) : ℝ) * w l := by
    intro l
    rw [sum_const, nsmul_eq_mul]
    gcongr
    exact_mod_cast next_card K m l hm
  have transp : (∑ k ∈ range K, ∑ l ∈ prev K m k, w l) =
      ∑ l ∈ range K, ∑ _k ∈ (range K).filter (fun k => l < k ∧ k < l + m), w l := by
    simp only [prev, sum_filter]; rw [sum_comm]
  calc
    _ ≤ ∑ k ∈ range K, ∑ l ∈ prev K m k, (w k + w l) :=
      sum_le_sum fun k _ => sum_le_sum fun l _ => twice_dot_le _ _
    _ = (∑ k ∈ range K, ∑ _l ∈ prev K m k, w k) +
      ∑ l ∈ range K, ∑ _k ∈ (range K).filter (fun k => l < k ∧ k < l + m), w l := by
          simp only [sum_add_distrib, transp]
    _ ≤ (∑ k ∈ range K, ((m - 1 : ℕ) : ℝ) * w k) + ∑ k ∈ range K, ((m - 1 : ℕ) : ℝ) * w k :=
      add_le_add (sum_le_sum fun k _ => row k) (sum_le_sum fun k _ => col k)
    _ = _ := by rw [←mul_sum]; dsimp [w]; ring

theorem ring_split (K m : ℕ) (hm : 0 < m) (v : ℕ → ℂ) :
    ‖∑ k ∈ range K, v k‖ ^ 2 ≤
      ((2 * m - 1 : ℕ) : ℝ) * (∑ k ∈ range K, ‖v k‖ ^ 2) +
      ∑ k ∈ range K, 2 * dot (v k) (∑ l ∈ range (k + 1 - m), v l) := by
  have step (k : ℕ) (hk : k ∈ range K) :
      2 * dot (v k) (∑ l ∈ range k, v l) =
      (∑ l ∈ prev K m k, 2 * dot (v k) (v l)) + 2 * dot (v k) (∑ l ∈ range (k + 1 - m), v l) := by
    have eq : prev K m k = Ico (k + 1 - m) k := by
      ext l
      simp only [prev, mem_filter, mem_range, mem_Ico]
      have := mem_range.mp hk
      omega
    rw [eq, dot_sum, dot_sum, ←mul_sum, ←mul_add, add_comm (∑ _ ∈ Ico _ _, _)]
    rw [sum_range_add_sum_Ico _ (by omega)]
  rw [triangular, sum_add_distrib]
  rw [sum_congr rfl step, sum_add_distrib]
  have hcoef : ((2 * m - 1 : ℕ) : ℝ) = 1 + 2 * ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * m - 1 = 1 + 2 * (m - 1) by omega)
  rw [hcoef, add_mul, one_mul]
  linarith [near_charge K m hm v]

/-- The split for arbitrary chosen frequencies (not expanded into absolute
values before combining the inner prefix). -/
theorem frequency_split {α} (S : Finset α) (K m : ℕ) (hm : 0 < m) (v : ℕ → α → ℂ) :
    (∑ a ∈ S, ‖∑ k ∈ range K, v k a‖ ^ 2) ≤
      ((2 * m - 1 : ℕ) : ℝ) * (∑ k ∈ range K, ∑ a ∈ S, ‖v k a‖ ^ 2) +
      ∑ k ∈ range K, ∑ a ∈ S, 2 * dot (v k a) (∑ l ∈ range (k + 1 - m), v l a) := by
  have h := sum_le_sum (s := S) fun a _ => ring_split K m hm (fun k=>v k a)
  simp only [sum_add_distrib, ←mul_sum] at h
  rw [sum_comm (s := S) (t := range K), sum_comm (s := S) (t := range K)] at h
  simpa only [←mul_sum] using h

/-- Negative-sign Fourier coefficient used in the physical-grid energy. -/
def amp {n : ℕ} (start : ℤ) (v : Fin n → ℂ) (p : Fraction) : ℂ :=
  ∑ j : Fin n, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
    ((start : ℂ) + j.val) * p.1 / p.2) * v j

def piece {n : ℕ} (label : Fin n → ℕ) (k : ℕ) (v : Fin n → ℂ) (i : Fin n) : ℂ :=
  if label i = k then v i else 0

def prefixPiece {n : ℕ} (label : Fin n → ℕ) (b : ℕ) (v : Fin n → ℂ) (i : Fin n) : ℂ :=
  if label i < b then v i else 0

theorem amp_prefix_sum {n : ℕ} (start : ℤ) (label : Fin n → ℕ) (b : ℕ)
    (v : Fin n → ℂ) (p : Fraction) :
    (∑ k ∈ range b, amp start (piece label k v) p) =
        amp start (prefixPiece label b v) p := by
  classical
  unfold amp
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [←mul_sum]
  congr 1
  simp [piece, prefixPiece, mem_range]

theorem amp_ring_sum {n K : ℕ} (start : ℤ) (label : Fin n → ℕ)
    (hlabel : ∀ i, label i < K) (v : Fin n → ℂ) (p : Fraction) :
    amp start v p = ∑ k ∈ range K, amp start (piece label k v) p := by
  rw [amp_prefix_sum]
  congr 1
  funext i
  simp [prefixPiece, hlabel]

theorem dot_eq_re_mul_conj (x y : ℂ) : dot x y = (x * (starRingEnd ℂ) y).re := by
  simp [dot, Complex.mul_re]

/-- Partition a physical input by any labels. The far term contains a single
Fourier coefficient of the entire inner prefix, with the original signs. -/
theorem physical_partition_split {α} {n K : ℕ} (S : Finset α) (fraction : α → Fraction)
    (start : ℤ) (label : Fin n → ℕ) (hlabel : ∀ i, label i < K)
    (v : Fin n → ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ a ∈ S, energy start v (fraction a)) ≤
      ((2 * m - 1 : ℕ) : ℝ) * (∑ k ∈ range K, ∑ a ∈ S, energy start (piece label k v) (fraction
        a)) +
      ∑ k ∈ range K, ∑ a ∈ S, 2 * dot (amp start (piece label k v) (fraction a))
        (amp start (prefixPiece label (k + 1 - m) v) (fraction a)) := by
  have eb (w : Fin n → ℂ) (a : α) : energy start w (fraction a) =
      ‖amp start w (fraction a)‖ ^ 2 := rfl
  simp only [eb]
  conv_lhs => arg 2; intro a; rw [amp_ring_sum start label hlabel v]
  simpa only [amp_prefix_sum] using frequency_split S K m hm
    (fun k a => amp start (piece label k v) (fraction a))

/-- Actual high-frequency grid of a deterministic threshold cut; no distribution
on the underlying rank placement and no arithmetic restrictions on its gaps. -/
theorem actual_cut_high_split {n K : ℕ} (p : RankPlacement n) (T h D : ℕ)
    (label : Fin n → ℕ) (hlabel : ∀ i, label i < K) (m : ℕ) (hm : 0 < m) :
    let v := fun i : Fin n => (RoughGapEndpoint.slotError p T i : ℂ)
    (∑ a ∈ Actual214.highGrid h D, energy 0 v (a, h)) ≤
      ((2 * m - 1 : ℕ) : ℝ) *
        (∑ k ∈ range K, ∑ a ∈ Actual214.highGrid h D, energy 0 (piece label k v) (a, h)) +
      ∑ k ∈ range K, ∑ a ∈ Actual214.highGrid h D,
        2 * dot (amp 0 (piece label k v) (a, h)) (amp 0 (prefixPiece label (k + 1 - m) v) (a, h)) :=
  physical_partition_split (Actual214.highGrid h D) (fun a=>(a, h)) 0 label hlabel _ m hm

end Shellsort.HarvestAnnularSplit

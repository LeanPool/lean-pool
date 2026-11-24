/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.RoughGapEndpoint

/-! Summing the exact phase over all rank cuts gives a signed, nonpositive
periodic correction to the total post-pass square displacement. -/
@[expose] public noncomputable section
namespace Shellsort.RoughGapEndpoint
open Finset

def periodicPenalty (h : ℕ) (x : ℤ) : ℤ :=
  let u := x % (h : ℤ)
  u * ((h : ℤ) - u)

theorem periodicPenalty_nonneg {h : ℕ} (hh : 0 < h) (x : ℤ) :
    0 ≤ periodicPenalty h x := by
  have H : (0 : ℤ) < h := by exact_mod_cast hh
  exact mul_nonneg (Int.emod_nonneg _ H.ne') (sub_nonneg.mpr (Int.emod_lt_of_pos _ H).le)

private theorem penalty_diff {h : ℕ} (hh : 0 < h) (x : ℤ) :
    periodicPenalty h x - periodicPenalty h (x + 1) = 2 * (x % (h : ℤ)) + 1 - h := by
  have H : (0 : ℤ) < h := by exact_mod_cast hh
  let a := x % (h : ℤ)
  have ha : 0 ≤ a := Int.emod_nonneg _ H.ne'
  have hb : a < h := Int.emod_lt_of_pos _ H
  have hm : (x + 1) % (h : ℤ) = (a + 1) % (h : ℤ) := by simp [a]
  unfold periodicPenalty
  rw [hm]
  change a * (h - a) - ((a + 1) % (h : ℤ)) * ((h : ℤ) - (a + 1) % (h : ℤ)) = 2 * a + 1 - h
  by_cases top : a + 1 = (h : ℤ)
  · rw [top]; simp; nlinarith
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    ring

private theorem corrected_phase {h : ℕ} (hh : 0 < h) (i T : ℕ) :
    phase h T (i % h) + 1 = 2 * (((i : ℤ) - T) % (h : ℤ)) + 1 - h := by
  let r := i % h
  let a := residuePrefixCount h r T
  have H := counted_residual_bounds h r T hh (Nat.mod_lt i hh)
  have he : (r : ℤ) + (h : ℤ) * (i / h : ℕ) = i := by exact_mod_cast Nat.mod_add_div i h
  have inner : ((r : ℤ) + (h : ℤ) * a - T) % h = ((i : ℤ) - T) % h := by
    have ht : (r : ℤ) + (h : ℤ) * a - T =
        ((i : ℤ) - T) + ((a : ℤ) - (i / h : ℕ)) * (h : ℤ) := by rw [← he]; ring
    rw [ht, Int.add_mul_emod_self_right]
  have hl : 0 ≤ (r : ℤ) + (h : ℤ) * a - T := by dsimp only [a]; omega
  have hu : (r : ℤ) + (h : ℤ) * a - T < h := by dsimp only [a]; omega
  rw [Int.emod_eq_of_lt hl hu] at inner
  unfold phase
  change 2 * ((r : ℤ) + h * a - T) - h + 1 = _
  rw [inner]; ring

private theorem sum_telescoping_from (f : ℕ → ℤ) {x n : ℕ} (hx : x ≤ n) :
    (∑ t ∈ range n, (f (t + 1) - f t) * (if x ≤ t then 1 else 0)) = f n - f x := by
  induction n, hx using Nat.le_induction with
  | base =>
    rw [sum_eq_zero]
    · omega
    · intro t ht
      simp [not_le.mpr (mem_range.mp ht)]
  | succ n hn ih =>
    rw [sum_range_succ, ih]
    simp only [hn, ite_true, mul_one]
    ring

private theorem slotCorrection {n h : ℕ} (p : RankPlacement n) (hh : 0 < h) (i : Fin n) :
    (∑ t ∈ range n, (phase h (t + 1) (i.val % h) + 1) * slotError p (t + 1) i) =
      -periodicPenalty h ((i.val : ℤ) - (p.symm i).val) := by
  let f := fun t : ℕ => periodicPenalty h ((i.val : ℤ) - t)
  have hd (t : ℕ) : phase h (t + 1) (i.val % h) + 1 = f (t + 1) - f t := by
    rw [corrected_phase hh, ← penalty_diff hh]
    dsimp only [f]
    congr 2
    push_cast
    ring
  simp_rw [hd, slotError, threshold_mem, Nat.lt_succ_iff, mul_sub]
  rw [sum_sub_distrib, sum_telescoping_from f (p.symm i).isLt.le,
    sum_telescoping_from f i.isLt.le]
  simp [f, periodicPenalty]

private theorem cutCorrection {n h : ℕ} (p : RankPlacement n) (T : ℕ)
    (hT : T ≤ n) (hh : 0 < h) :
    (∑ r : Fin h, phase h T r.val * residueError p h T r.val) =
      ∑ i : Fin n, (phase h T (i.val % h) + 1) * slotError p T i := by
  calc
    _ = ∑ r : Fin h, (phase h T r.val + 1) * residueError p h T r.val := by
      simp_rw [add_mul, one_mul]
      rw [sum_add_distrib, residueError_sum p T hT hh, add_zero]
    _ = _ := by
      simp_rw [residueError_eq_sum p T _ hT, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      let a : Fin h := ⟨i.val % h, Nat.mod_lt _ hh⟩
      have he (r : Fin h) : i.val % h = r.val ↔ a = r := (Fin.ext_iff (a := a) (b := r)).symm
      simp [he, mul_ite, a]

/-- Unconditional identity for an actual finite gap pass. -/
theorem gapSort_square_energy {n h : ℕ} (p : RankPlacement n) (hh : 0 < h) :
    RoughGapScaleAssembly.squareDisplacement (gapSort p h) =
      (h : ℤ) * (∑ t ∈ range n, ∑ r : Fin h, residueError p h (t + 1) r.val ^ 2) -
        ∑ i : Fin n, periodicPenalty h ((i.val : ℤ) - (p.symm i).val) := by
  rw [gapSort_squareDisplacement_exact p hh]
  simp_rw [sum_add_distrib]
  rw [sub_eq_add_neg]
  simp_rw [← mul_sum]
  congr 1
  calc
    _ = ∑ t ∈ range n, ∑ i : Fin n, (phase h (t + 1) (i.val % h) + 1) * slotError p (t + 1) i := by
      apply sum_congr rfl
      intro t ht
      exact cutCorrection p (t + 1) (mem_range.mp ht) hh
    _ = _ := by
      rw [sum_comm]
      simp_rw [slotCorrection p hh]
      rw [sum_neg_distrib]

theorem gapSort_square_le_energy {n h : ℕ} (p : RankPlacement n) (hh : 0 < h) :
    RoughGapScaleAssembly.squareDisplacement (gapSort p h) ≤
      (h : ℤ) * (∑ t ∈ range n, ∑ r : Fin h, residueError p h (t + 1) r.val ^ 2) := by
  rw [gapSort_square_energy p hh]
  exact sub_le_self _ (sum_nonneg (fun _ _ => periodicPenalty_nonneg hh _))



end Shellsort.RoughGapEndpoint

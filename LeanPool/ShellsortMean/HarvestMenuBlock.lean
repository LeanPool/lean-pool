/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.HarvestAnnularSplitActual
public import LeanPool.ShellsortMean.HarvestNearMean
public import LeanPool.ShellsortMean.HarvestLowMultiplicity
public import LeanPool.ShellsortMean.HarvestCutSpectrum
public import LeanPool.ShellsortMean.HarvestLinearLowMenu

/-! Actual geometric menu, actual dyadic pieces, and actual state after the
two retained passes. Sum the cut rewards before using the signed correction. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestMenuBlock
open Finset Actual214 RoughGapEndpoint RoughGapDenominatorAverage HarvestActualRings

/-- The admissible third gaps after the two retained passes at index `j`. -/
def choices (j : ℕ) := window (gap j) (Nat.gcd (gap (j + 2)) (gap (j + 1)))

/-- The sum of absolute slot errors at the chosen rank threshold. -/
def mass {n : ℕ} (p : RankPlacement n) (T : ℕ) : ℝ := ∑ i, |(slotError p T i : ℝ)|

/-- The high-frequency bound in terms of threshold mass and its cut moment. -/
def highBound (c D m : ℕ) (s V : ℝ) : ℝ :=
  ((2 * m - 1 : ℕ) : ℝ) * (18800 * (32 * (c : ℝ) * s + (4 * Real.pi / D) * (2 * c * s + 4 * V))) +
    (4 * c * s + (8 * (2 + (D : ℝ) ^ 2) * (1 / (2 : ℝ) ^ m)) * V)

private theorem choices_bounds {j h : ℕ} (hc : 9400 ≤ gap j) (hh : h ∈ choices j) :
    0 < h ∧ h ≤ 2 * gap j := by
  obtain ⟨lo, hi⟩ := mem_Icc.mp (mem_filter.mp hh).1
  omega

/-- The high-denominator bound on one fixed, genuine cut, averaged over
the recurrence's original menu. No assumption about a Fourier cross term. -/
theorem actual_menu_high_energy {n T D m : ℕ} (j : ℕ) (hc : 9400 ≤ gap j)
    (hd : 0 < D) (hm : 0 < m) (ht : T ≤ n) (p : RankPlacement n) :
    (∑ h ∈ choices j, ∑ a ∈ highGrid h D,
      energy 0 (fun i : Fin n => (slotError p T i : ℂ)) (a, h)) / ((choices j).card : ℝ) ≤
      highBound (gap j) D m (mass p T) (cutMoment p T : ℝ) := by
  let G := choices j
  let s := mass p T
  let w := (8 * (2 + (D : ℝ) ^ 2) * (1 / (2 : ℝ) ^ m)) * (cutMoment p T : ℝ)
  let N : ℝ := (2 * m - 1 : ℕ)
  let e (k : Fin (n + 1)) (h : ℕ) := ∑ a ∈ highGrid h D,
    energy 0 (fun i => (ringVec ht (gap_pos j) p k i : ℂ)) (a, h)
  let A (h : ℕ) := ∑ a ∈ highGrid h D, energy 0 (fun i : Fin n => (slotError p T i : ℂ)) (a, h)
  have nonneg : 0 ≤ s := by dsimp [s, mass]; positivity
  have card : (G.card : ℝ) ≠ 0 := by
    have h : gap j / 9400 ≤ G.card := actual_window_card j hc
    exact_mod_cast (show G.card ≠ 0 by omega)
  have one (h : ℕ) (hh : h ∈ G) : A h ≤ N * (∑ k, e k h) + (4 * (gap j : ℝ) * s + w) := by
    have hb := choices_bounds hc hh
    let : NeZero h := ⟨hb.1.ne'⟩
    have fixed := HarvestAnnularSplit.actual_high_diagonal_and_moment
      (h := h) ht (gap_pos j) p D m hm
    have upper : (h : ℝ) ≤ 2 * (gap j : ℝ) := by exact_mod_cast hb.2
    apply fixed.trans
    change N * (∑ k, e k h) + (2 * (h : ℝ) * s + w) ≤ _
    exact add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_right
      (show 2 * (h : ℝ) ≤ 4 * (gap j : ℝ) by linarith) nonneg) le_rfl)
  have nearBound := HarvestNearMean.actual_menu_ring_energy j hc hd ht p
  change (∑ k, (∑ h ∈ G, e k h) / (G.card : ℝ)) ≤ _ at nearBound
  change (∑ h ∈ G, A h) / (G.card : ℝ) ≤ _
  calc
    _ ≤ (∑ h ∈ G, (N * (∑ k, e k h) + (4 * (gap j : ℝ) * s + w))) / (G.card : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum one) (by positivity)
    _ = N * (∑ k, (∑ h ∈ G, e k h) / (G.card : ℝ)) + (4 * (gap j : ℝ) * s + w) := by
      rw [sum_add_distrib, ←mul_sum, sum_const, nsmul_eq_mul, ←sum_div,
          sum_comm (s := G) (t := univ)]
      field_simp
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left nearBound
      (show 0 ≤ N by dsimp [N]; positivity)) le_rfl

/-- One physical block: a deterministic state, the two actual retained gaps,
and the uniformly chosen third gap. The low term uses the incoming mass,
whereas the high term is computed on the common post-retained state. -/
theorem block_square_with_low {n D m : ℕ} (j : ℕ) (hc : 9400 ≤ gap j)
    (hd : 0 < D) (hm : 0 < m) (p : RankPlacement n) (K : ℝ)
    (low : ∀ T ≤ n, (∑ h ∈ choices j, ∑ a ∈ lowGrid h D, energy 0
      (fun i : Fin n => (slotError (gapSort (gapSort p (gap (j + 2))) (gap (j + 1))) T i : ℂ))
        (a, h)) /
        ((choices j).card : ℝ) ≤ K * mass p T) :
    let z := gapSort (gapSort p (gap (j + 2))) (gap (j + 1))
    (∑ h ∈ choices j, (RoughGapScaleAssembly.squareDisplacement (gapSort z h) : ℝ)) /
      ((choices j).card : ℝ) ≤ ∑ t ∈ range n,
        (K * mass p (t + 1) +
        highBound (gap j) D m (mass z (t + 1)) (cutMoment z (t + 1) : ℝ)) := by
  intro z
  let G := choices j
  let E (t h a : ℕ) := energy 0 (fun i : Fin n => (slotError z (t + 1) i : ℂ)) (a, h)
  let L (t h : ℕ) := ∑ a ∈ lowGrid h D, E t h a
  let H (t h : ℕ) := ∑ a ∈ highGrid h D, E t h a
  have one (h : ℕ) (hh : h ∈ G) : (RoughGapScaleAssembly.squareDisplacement (gapSort z h) : ℝ) ≤
      ∑ t ∈ range n, (L t h + H t h) := by
    apply (HarvestCutSpectrum.square_le_physical_spectrum z (choices_bounds hc hh).1).trans_eq
    exact sum_congr rfl fun t _ => nonzero_grid_split h D (E t h)
  calc
    _ ≤ (∑ h ∈ G, ∑ t ∈ range n, (L t h + H t h)) / (G.card : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum one) (by positivity)
    _ = ∑ t ∈ range n, ((∑ h ∈ G, L t h) / (G.card : ℝ) + (∑ h ∈ G, H t h) / (G.card : ℝ)) := by
      rw [sum_comm]
      simp only [sum_add_distrib, sum_div, add_div]
    _ ≤ _ := by
      apply sum_le_sum
      intro t ht
      exact add_le_add (low (t + 1) (mem_range.mp ht))
        (actual_menu_high_energy j hc hd hm (mem_range.mp ht) z)

theorem actual_block_square_linear {n D m : ℕ} (j : ℕ) (hc : 9400 ≤ gap j)
    (hd : 0 < D) (hm : 0 < m) (p : RankPlacement n) :
    let z := gapSort (gapSort p (gap (j + 2))) (gap (j + 1))
    (∑ h ∈ choices j, (RoughGapScaleAssembly.squareDisplacement (gapSort z h) : ℝ)) /
      ((choices j).card : ℝ) ≤ ∑ t ∈ range n,
      ((2 * 18800 * (gap (j + 2) : ℝ) * D) * mass p (t + 1) +
        highBound (gap j) D m (mass z (t + 1)) (cutMoment z (t + 1) : ℝ)) :=
  block_square_with_low j hc hd hm p (2 * 18800 * (gap (j + 2) : ℝ) * (D : ℝ))
    (fun T hT => actual_low_linear_mean p T hT j hc)



end Shellsort.HarvestMenuBlock

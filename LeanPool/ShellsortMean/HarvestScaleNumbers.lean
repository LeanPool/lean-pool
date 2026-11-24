/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestAggregateBudget
public import LeanPool.ShellsortMean.RoughGapPredeterminedSelection
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Calibrate the two actual Fourier coefficients using pi < 4. -/
@[expose] public noncomputable section
namespace Shellsort.HarvestScaleNumbers
open Actual214
open Finset RoughGapScaleAssembly HarvestMenuBlock HarvestAggregateBudget

theorem retained_ratio (j : ℕ) (hc : 9400 ≤ gap j) : gap (j + 2) ≤ 9 * gap j := by
  have a := scaled_next_bounds (gap j)
  have b := scaled_next_bounds (nextGap (gap j))
  change nextGap (nextGap (gap j)) ≤ _
  omega

/-- The two coefficients multiplying the initial F and Q, respectively.
The numerical energy contraction is independent of n and the group index. -/
theorem calibrated_coefficients (c g : ℕ) (hg : g ≤ 9 * c) :
    let D : ℕ := 2 ^ 79
    let m : ℕ := 324
    4 * 18800 * (g : ℝ) * (D : ℝ) ^ 2 + (c : ℝ) * (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 *
      Real.pi / D) + 4)
        ≤ (2 : ℝ) ^ 179 * c ∧
    ((2 * m - 1 : ℕ) : ℝ) * 18800 * (8 * Real.pi / D) + 4 * (2 + (D : ℝ) ^ 2) / (2 : ℝ) ^ m
        ≤ 1 / (2 : ℝ) ^ 47 := by
  intro D m
  have upper : (g : ℝ) ≤ 9 * (c : ℝ) := by exact_mod_cast hg
  have num : 36 * 18800 * (D : ℝ) ^ 2 + (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 * Real.pi / D) + 4)
      ≤ (2 : ℝ) ^ 179 := by
    norm_num [D, m]
    linarith only [Real.pi_lt_four]
  constructor
  · calc
      _ ≤ 4 * 18800 * (9 * (c : ℝ)) * (D : ℝ) ^ 2 + (c : ℝ) * (((2 * m - 1 : ℕ) : ℝ) * 18800 *
        (32 + 8 * Real.pi / D) + 4) := by gcongr
      _ = (36 * 18800 * (D : ℝ) ^ 2 + (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 * Real.pi / D) +
        4)) * c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right num (by positivity)
  · conv_lhs => arg 2; rw [show m = 162 + 162 by decide, pow_add]
    norm_num [D, m]
    linarith only [Real.pi_lt_four]

/-- The three-pass block with two retained gaps and the selected gap `h`. -/
def block {n : ℕ} (j h : ℕ) (p : RankPlacement n) :=
  gapSort (gapSort (gapSort p (gap (j + 2))) (gap (j + 1))) h

private theorem choose_below (G : Finset ℕ) (nonempty : G.Nonempty)
    (r : ℕ → ℝ) (b : ℝ) (bound : (∑ h ∈ G, r h) ≤ (G.card : ℝ) * b) :
    ∃ h ∈ G, r h ≤ b := by
  apply exists_le_of_sum_le nonempty (g := fun _ => b)
  simpa only [sum_const, nsmul_eq_mul] using bound

/-- No spectral premise: the incoming permutation alone determines the
normalized comparison-potential budget for the uniformly sampled third gap. -/
theorem actual_block_contraction {n : ℕ} (j : ℕ) (hc : 9400 ≤ gap j) (p : RankPlacement n) :
    (∑ h ∈ choices j, (squareDisplacement (block j h p) : ℝ)) / ((choices j).card : ℝ) ≤
      (2 : ℝ) ^ 179 * (gap j : ℝ) * footrule p + (1 / (2 : ℝ) ^ 47) * (squareDisplacement p :
        ℝ) := by
  have cf := calibrated_coefficients (gap j) (gap (j + 2)) (retained_ratio j hc)
  have Fpos : 0 ≤ footrule p := by unfold footrule transport; positivity
  have Qpos : 0 ≤ (squareDisplacement p : ℝ) := by
    exact_mod_cast (show 0 ≤ squareDisplacement p by unfold squareDisplacement; positivity)
  apply (actual_block_budget (D := 2 ^ 79) (m := 324) j hc (by decide) (by decide) p).trans
  exact add_le_add (mul_le_mul_of_nonneg_right cf.1 Fpos) (mul_le_mul_of_nonneg_right cf.2 Qpos)

/-- Stronger coefficient obtained by charging each primitive packet as one. -/
theorem actual_linear_block_contraction {n : ℕ} (j : ℕ) (hc : 9400 ≤ gap j) (p : RankPlacement n) :
    (∑ h ∈ choices j, (squareDisplacement (block j h p) : ℝ)) / ((choices j).card : ℝ) ≤
      (2 : ℝ) ^ 98 * (gap j : ℝ) * footrule p + (1 / (2 : ℝ) ^ 47) * (squareDisplacement p :
        ℝ) := by
  let D : ℕ := 2 ^ 79
  let m : ℕ := 324
  have cf := (calibrated_coefficients _ _ (retained_ratio j hc)).2
  have fpos : 0 ≤ footrule p := by unfold footrule transport; positivity
  have qpos : 0 ≤ (squareDisplacement p : ℝ) := by
    exact_mod_cast (show 0 ≤ squareDisplacement p by unfold squareDisplacement; positivity)
  have g : (gap (j + 2) : ℝ) ≤ 9 * (gap j : ℝ) := by exact_mod_cast retained_ratio j hc
  have num : (18 * 18800 * (D : ℝ) + (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 * Real.pi / D) +
    4)) ≤ (2 : ℝ) ^ 98 := by
    norm_num [D, m]
    linarith only [Real.pi_lt_four]
  have upper : 2 * 18800 * (gap (j + 2) : ℝ) * D + highFoot (gap j) D m ≤ (2 : ℝ) ^ 98 * gap j := by
    unfold highFoot
    calc
      _ ≤ 2 * 18800 * (9 * (gap j : ℝ)) * D + (gap j : ℝ) * (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32
        + 8 * Real.pi / D) + 4) := by gcongr
      _ = (18 * 18800 * (D : ℝ) + (((2 * m - 1 : ℕ) : ℝ) * 18800 * (32 + 8 * Real.pi / D) + 4)) *
        (gap j : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right num (by positivity)
  apply (actual_block_budget_linear (D := D) (m := m) j hc (by decide) (by decide) p).trans
  exact add_le_add (mul_le_mul_of_nonneg_right upper fpos) (mul_le_mul_of_nonneg_right cf qpos)

/-- For any fixed prefix state map P, one common candidate works after
averaging over the original uniform permutations. Its choice is before the
input. This is a one-block theorem, even when P is highly non-uniform. -/
private theorem select_with_block {n : ℕ} (hn : 0 < n) (P : RankPlacement n → RankPlacement n)
    (j : ℕ) (hc : 9400 ≤ gap j) (K : ℝ) (kpos : 0 ≤ K)
    (pointwise : ∀ p : RankPlacement n,
      (∑ h ∈ choices j, (squareDisplacement (block j h p) : ℝ)) / ((choices j).card : ℝ) ≤
       K * (gap j : ℝ) * footrule p + (1 / (2 : ℝ) ^ 47) * (squareDisplacement p : ℝ)) :
    let x := uniformAverage (fun p => RoughGapSelection.energy (P p))
    ∃ h ∈ choices j, uniformAverage (fun p => RoughGapSelection.energy (block j h (P p))) ≤
      (1 / (2 : ℝ) ^ 47) * x + K * (gap j : ℝ) * Real.sqrt x := by
  intro x
  let G := choices j
  let F := fun p => RoughGapSelection.mass (P p)
  let Q := fun p => RoughGapSelection.energy (P p)
  let reward := fun h p => RoughGapSelection.energy (block j h (P p))
  let β := K * (gap j : ℝ)
  let α := 1 / (2 : ℝ) ^ 47
  have card : 0 < G.card := by
    have h : gap j / 9400 ≤ G.card := actual_window_card j hc
    omega
  have cp : (0 : ℝ) < G.card := by exact_mod_cast card
  have np : (0 : ℝ) < n := by exact_mod_cast hn
  have point (p : RankPlacement n) :
      (∑ h ∈ G, reward h p) ≤ (G.card : ℝ) * (β * F p + α * Q p) := by
    have b := (div_le_iff₀ cp).mp (pointwise (P p))
    dsimp [reward, RoughGapSelection.energy, F, Q, RoughGapSelection.mass]
    rw [←sum_div]
    apply (div_le_iff₀ np).mpr
    convert b using 1; dsimp [β, α]; field_simp
  have avg := uniformAverage_mono _ _ point
  have swap : uniformAverage (fun p => ∑ h ∈ G, reward h p) =
      ∑ h ∈ G, uniformAverage (reward h) := by unfold uniformAverage; rw [sum_comm, sum_div]
  rw [swap, uniformAverage_const_mul, uniformAverage_add, uniformAverage_const_mul,
      uniformAverage_const_mul] at avg
  have rootBound : uniformAverage F ≤ Real.sqrt x :=
    RoughGapSelection.prefix_mean_mass_le_root_energy hn P
  change ∃ h ∈ G, uniformAverage (reward h) ≤ α * x + β * Real.sqrt x
  have fbound := mul_le_mul_of_nonneg_left rootBound (show 0 ≤ β by dsimp [β]; positivity)
  have lim : (G.card : ℝ) * (β * uniformAverage F + α * uniformAverage Q) ≤
      (G.card : ℝ) * (α * x + β * Real.sqrt x) := by
    apply mul_le_mul_of_nonneg_left _ cp.le
    change β * uniformAverage F + α * x ≤ _
    linarith only [fbound]
  exact choose_below G (card_pos.mp card) (fun h => uniformAverage (reward h)) _ (avg.trans lim)

theorem select_actual_block {n : ℕ} (hn : 0 < n) (P : RankPlacement n → RankPlacement n)
    (j : ℕ) (hc : 9400 ≤ gap j) :
    let x := uniformAverage (fun p => RoughGapSelection.energy (P p))
    ∃ h ∈ choices j, uniformAverage (fun p => RoughGapSelection.energy (block j h (P p))) ≤
      (1 / (2 : ℝ) ^ 47) * x + (2 : ℝ) ^ 179 * (gap j : ℝ) * Real.sqrt x :=
  select_with_block hn P j hc _ (by positivity) (actual_block_contraction j hc)

theorem select_actual_linear_block {n : ℕ} (hn : 0 < n) (P : RankPlacement n → RankPlacement n)
    (j : ℕ) (hc : 9400 ≤ gap j) :
    let x := uniformAverage (fun p => RoughGapSelection.energy (P p))
    ∃ h ∈ choices j, uniformAverage (fun p => RoughGapSelection.energy (block j h (P p))) ≤
      (1 / (2 : ℝ) ^ 47) * x + (2 : ℝ) ^ 98 * (gap j : ℝ) * Real.sqrt x :=
  select_with_block hn P j hc _ (by positivity) (actual_linear_block_contraction j hc)






end Shellsort.HarvestScaleNumbers

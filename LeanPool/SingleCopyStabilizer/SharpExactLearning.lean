/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.ExactLearning
public import LeanPool.SingleCopyStabilizer.GeometricTailBounds
public import LeanPool.SingleCopyStabilizer.GeometricDomination


/-!
# Exact label compression with a sharp leading round count

The numerical budget has leading term `2n` rounds and `4n` copies. The tail
bound is for the explicit uniform-X-label process in `ExactLearning`; the
connection of that process to Born-rule circuit execution is proved separately.
-/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.SharpExactLearning

open GeometricTailBounds

/-- The reciprocal progress-rate bound for `n` qubits. -/
def meanBound (n : ℕ) : ℝ := 2 * (n : ℝ) + 4

/-- Explicit round budget preserving the leading coefficient two. -/
def roundBudget (n : ℕ) (δ : ℝ) : ℕ := confidenceBudget (meanBound n) δ

/-- Two fresh copies per round, followed by one final computational readout. -/
def copyBudget (n : ℕ) (δ : ℝ) : ℕ := 2 * roundBudget n δ + 1

theorem meanBound_pos (n : ℕ) : 0 < meanBound n := by
  unfold meanBound
  positivity

/-- Expanded round budget with no hidden asymptotic constants. -/
theorem roundBudget_formula (n : ℕ) (δ : ℝ) :
    roundBudget n δ =
      ⌈2 * (n : ℝ) + 4 + 8 * Real.sqrt ((2 * (n : ℝ) + 4) * Real.log (1 / δ)) +
        64 * Real.log (1 / δ)⌉₊ := by
  unfold roundBudget confidenceBudget confidenceDeviation meanBound
  congr 1
  ring

/-- The logarithmic confidence parameter is nonnegative on the intended range. -/
theorem confidence_log_nonneg (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    0 ≤ Real.log (1 / δ) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hδ).2
  simpa using hδmax

/-- Rounding adds less than one round to the explicit real-valued budget. -/
theorem roundBudget_upper (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    (roundBudget n δ : ℝ) <
      2 * (n : ℝ) + 5 + 8 * Real.sqrt ((2 * (n : ℝ) + 4) * Real.log (1 / δ)) +
        64 * Real.log (1 / δ) := by
  have hM := meanBound_pos n
  have hlog := confidence_log_nonneg δ hδ hδmax
  have hdev := confidenceDeviation_nonneg (meanBound n) _ hM.le hlog
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ meanBound n + confidenceDeviation (meanBound n) (Real.log (1 / δ)) by linarith)
  change (roundBudget n δ : ℝ) < _ at hceil
  dsimp [confidenceDeviation, meanBound] at hceil
  linarith

/-- The resulting copy budget has leading coefficient four. -/
theorem copyBudget_upper (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    (copyBudget n δ : ℝ) <
      4 * (n : ℝ) + 11 + 16 * Real.sqrt ((2 * (n : ℝ) + 4) * Real.log (1 / δ)) +
        128 * Real.log (1 / δ) := by
  have := roundBudget_upper n δ hδ hδmax
  simp only [copyBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

/-- An explicit universal-constant copy bound, valid for at least one qubit.
The constant is conservative; `copyBudget_upper` retains the sharper leading
coefficient four and square-root confidence term. -/
theorem copyBudget_linear (n : ℕ) (hn : 1 ≤ n) (δ : ℝ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    (copyBudget n δ : ℝ) < 136 * ((n : ℝ) + Real.log (1 / δ)) := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := confidence_log_nonneg δ hδ hδmax
  have hsqrt : Real.sqrt ((2 * (n : ℝ) + 4) * Real.log (1 / δ)) ≤
      ((2 * (n : ℝ) + 4) + Real.log (1 / δ)) / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg ((2 * (n : ℝ) + 4) - Real.log (1 / δ))]
  have hbudget := copyBudget_upper n δ hδ hδmax
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The exact process's rank is bounded by the number of qubits. -/
theorem rank_le_qubit_count (s : ExactLearning.State ι) :
    ExactLearning.rank s ≤ Fintype.card ι := Nat.sub_le _ _

/-- Every needed progress-rate estimate is proved for the exact process. -/
theorem exact_progress_parameter (s : ExactLearning.State ι) :
    FiniteProbability.progressProbability (ExactLearning.rank s) ≤
      ExactLearning.process.progressMass s :=
  ExactLearning.progress_mass_ge_rank_parameter s

omit [DecidableEq ι] in
/-- The reciprocal-sum hypothesis is discharged for every exact-process state. -/
theorem exact_process_mean_bound (s : ExactLearning.State ι) :
    (∑ j ∈ Finset.range (ExactLearning.rank s),
      1 / FiniteProbability.progressProbability (j + 1)) ≤ meanBound (Fintype.card ι) :=
  exact_rate_sum_bound _ _ (rank_le_qubit_count s)

/-- The explicit exact-learning label process succeeds with confidence
`1-δ` at every round count at least the sharp-leading-term budget. All
progress-rate and reciprocal-sum hypotheses are proved, not assumed. -/
theorem compression_failure_probability_after_budget (s : ExactLearning.State ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) (T : ℕ)
    (hT : roundBudget (Fintype.card ι) δ ≤ T) :
    ExactLearning.process.failureProbability T s ≤ δ := by
  let M : ℝ := meanBound (Fintype.card ι)
  let L : ℝ := Real.log (1 / δ)
  let deviation : ℝ := confidenceDeviation M L
  let lambda : ℝ := chosenTilt M deviation
  have hM : 0 < M := meanBound_pos _
  have hL : 0 ≤ L := confidence_log_nonneg δ hδ hδmax
  have hdev : 0 ≤ deviation := confidenceDeviation_nonneg M L hM.le hL
  obtain ⟨hlambda, hlambdamax⟩ := chosenTilt_bounds M deviation hM hdev
  have hrate : ∀ j, 0 < j → lambda < FiniteProbability.progressProbability j := by
    intro j hj
    exact chosenTilt_lt_rate M deviation _ hM hdev
      (FiniteProbability.progress_probability_ge_quarter j hj)
  have hdom := GeometricDomination.failure_probability_le_product
    FiniteProbability.progressProbability lambda hlambda hrate ExactLearning.process
    (show lambda ≤ 1 by dsimp [lambda]; linarith)
    (fun state _ => exact_progress_parameter state) T s
  have htime : M + confidenceDeviation M (Real.log (1 / δ)) ≤ (T : ℝ) := by
    have hceil : M + confidenceDeviation M (Real.log (1 / δ)) ≤
        (roundBudget (Fintype.card ι) δ : ℝ) := Nat.le_ceil _
    have hTreal : (roundBudget (Fintype.card ι) δ : ℝ) ≤ T := by exact_mod_cast hT
    exact hceil.trans hTreal
  have htail : GeometricDomination.productPotential FiniteProbability.progressProbability
      lambda (ExactLearning.rank s) * (1 - lambda) ^ T ≤ δ := by
    simpa only [GeometricDomination.productPotential, GeometricDomination.geometricFactor] using
      confidence_tail_bound (Finset.range (ExactLearning.rank s))
        (fun j => FiniteProbability.progressProbability (j + 1)) M δ T hM hδ hδmax
        (fun j _ => FiniteProbability.progress_probability_ge_quarter (j + 1) (by omega))
        (exact_process_mean_bound s) htime
  exact hdom.trans htail

/-- Exact label compression in `ceil(2n+4+8√((2n+4)log(1/δ))+64log(1/δ))`
rounds, with failure probability at most `δ`. -/
theorem compression_failure_probability (s : ExactLearning.State ι)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ 1) :
    ExactLearning.process.failureProbability (roundBudget (Fintype.card ι) δ) s ≤ δ :=
  compression_failure_probability_after_budget s δ hδ hδmax _ le_rfl

end LeanPool.SingleCopyStabilizer.SharpExactLearning

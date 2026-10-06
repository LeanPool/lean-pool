/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.NormalizedMinimalScale

/-!
# High-contrast homogenization: Provider.Quenched.CoupledMixingScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A coupled mixing-scale certificate

The mixing scale, its marginal tail, and its pathwise all-later certificate
belong to one witness.  Keeping these data together prevents replacing the
selected scale by an unrelated random variable with the same marginal tail.
-/

namespace HCPolySupport.HighContrast.Quenched

open Filter MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- One selected mixing scale together with the row series and bad events from
which it was constructed. -/
structure CoupledMixingScaleWitness
    (P : Measure Ω) (selectedRow : ℕ → Ω → ℝ)
    (cMix cd eta kappa delta : ℝ) where
  stoppingNormalization : ℝ
  normalization : ℝ
  scale : Ω → ℝ
  row : ℕ → Ω → ℝ
  tailSum : ℕ → Ω → ℝ
  bad : ℕ → Set Ω
  one_le_stoppingNormalization : 1 ≤ stoppingNormalization
  one_le_normalization : 1 ≤ normalization
  three_mul_stoppingNormalization_le :
    3 * stoppingNormalization ≤ normalization
  measurable_scale : Measurable scale
  one_le_scale : ∀ ω, 1 ≤ scale ω
  scale_tail : ∀ t : ℝ, 1 ≤ t →
    P.real {ω | cMix * t ≤ scale ω} ≤ Real.exp (-cd * t ^ eta)
  row_eq_selected : ∀ n ω, row n ω = selectedRow n ω
  row_nonneg : ∀ n ω, 0 ≤ row n ω
  hasSum_tail : ∀ᵐ ω ∂P, ∀ n,
    HasSum
      (fun j : ℕ =>
        (3 : ℝ) ^ (kappa * (j : ℝ)) * row (n + j) ω)
      (tailSum n ω)
  bad_eq : ∀ n, bad n = {ω | delta ≤ tailSum n ω}
  measurableSet_bad : ∀ n, MeasurableSet (bad n)
  eventually_not_mem_bad :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      stoppingNormalization * scale ω ≤ (3 : ℝ) ^ n → ω ∉ bad n

namespace CoupledMixingScaleWitness

/-- Membership in a selected bad event is the literal tail-sum threshold. -/
theorem mem_bad_iff
    {P : Measure Ω} {selectedRow : ℕ → Ω → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta)
    (n : ℕ) (ω : Ω) :
    ω ∈ W.bad n ↔ delta ≤ W.tailSum n ω := by
  simp only [W.bad_eq, Set.mem_ofPred_eq]

/-- Absence of a bad event makes the corresponding weighted tail sum strictly
smaller than its threshold. -/
theorem tailSum_lt_of_not_mem_bad
    {P : Measure Ω} {selectedRow : ℕ → Ω → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta)
    {n : ℕ} {ω : Ω} (hgood : ω ∉ W.bad n) :
    W.tailSum n ω < delta := by
  exact lt_of_not_ge (fun hdelta => hgood ((W.mem_bad_iff n ω).2 hdelta))

/-- Every nonnegative summand is bounded by the selected tail sum. -/
theorem weighted_row_le_tailSum
    {P : Measure Ω} {selectedRow : ℕ → Ω → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta)
    (n j : ℕ) (ω : Ω)
    (hsum : HasSum
      (fun i : ℕ =>
        (3 : ℝ) ^ (kappa * (i : ℝ)) * W.row (n + i) ω)
      (W.tailSum n ω)) :
    (3 : ℝ) ^ (kappa * (j : ℝ)) * W.row (n + j) ω ≤ W.tailSum n ω := by
  let f : ℕ → ℝ := fun i =>
    (3 : ℝ) ^ (kappa * (i : ℝ)) * W.row (n + i) ω
  have hf_nonneg : ∀ i, 0 ≤ f i := by
    intro i
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (W.row_nonneg _ _)
  have hsum' : HasSum f (W.tailSum n ω) := by
    simpa only [f] using hsum
  have hsingle : ∑ i ∈ ({j} : Finset ℕ), f i ≤ ∑' i, f i :=
    hsum'.summable.sum_le_tsum {j} (fun i _ => hf_nonneg i)
  simpa only [Finset.sum_singleton, hsum'.tsum_eq, f] using hsingle

/-- One later row is strictly controlled by the corresponding weighted-series
threshold whenever the starting event is good. -/
theorem weighted_row_lt_of_not_mem_bad
    {P : Measure Ω} {selectedRow : ℕ → Ω → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta)
    {n j : ℕ} {ω : Ω}
    (hsum : HasSum
      (fun i : ℕ =>
        (3 : ℝ) ^ (kappa * (i : ℝ)) * W.row (n + i) ω)
      (W.tailSum n ω))
    (hgood : ω ∉ W.bad n) :
    (3 : ℝ) ^ (kappa * (j : ℝ)) * W.row (n + j) ω < delta :=
  (W.weighted_row_le_tailSum n j ω hsum).trans_lt
    (W.tailSum_lt_of_not_mem_bad hgood)

/-- On one common full-measure event, the same selected mixing scale controls
every later weighted row. -/
theorem eventually_weighted_row_lt
    {P : Measure Ω} {selectedRow : ℕ → Ω → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta) :
    ∀ᵐ ω ∂P, ∀ n j : ℕ,
      W.stoppingNormalization * W.scale ω ≤ (3 : ℝ) ^ n →
        (3 : ℝ) ^ (kappa * (j : ℝ)) * W.row (n + j) ω < delta := by
  filter_upwards [W.hasSum_tail, W.eventually_not_mem_bad]
    with ω hsum hgood
  intro n j hn
  exact W.weighted_row_lt_of_not_mem_bad (hsum n) (hgood n hn)

end CoupledMixingScaleWitness

end

end HCPolySupport.HighContrast.Quenched

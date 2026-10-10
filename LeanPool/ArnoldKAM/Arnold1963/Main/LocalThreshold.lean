/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.HamiltonianLocalization
public import LeanPool.ArnoldKAM.Arnold1963.Main.LocalKAM

/-!
Choose a positive perturbation threshold on each geometric patch before the perturbation
is specified, using the existing numerical thresholds.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963
open Iteration
namespace HamiltonianPatch
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}

/-- The initial smallness seed selected from a Hamiltonian patch's numerical bounds. -/
def seed (c : HamiltonianPatch n H₀ ambient) (ρ : ℝ≥0) (κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (threshold5 n c.lower c.upper ρ κ c.typeConstant / 2)

/-- The positive perturbation threshold associated with a Hamiltonian patch. -/
def threshold (c : HamiltonianPatch n H₀ ambient) (ρ : ℝ≥0) (κ : ℝ) : ℝ :=
  initialPerturbationThreshold n c.lower c.upper ρ κ c.typeConstant

theorem threshold_pos (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) : 0 < c.threshold ρ κ :=
  initialPerturbationThreshold_pos hn c.lower_pos (zero_lt_one.trans c.upper_gt_one)
    hρ hκ (c.typeD hn).constant_pos

theorem seed_coe (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    (c.seed ρ κ : ℝ) = threshold5 n c.lower c.upper ρ κ c.typeConstant / 2 := by
  apply Real.coe_toNNReal _ (le_of_lt (half_pos ?_))
  exact threshold5_pos hn c.lower_pos (zero_lt_one.trans c.upper_gt_one)
    hρ hκ (c.typeD hn).constant_pos

theorem parameters (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1) :
    InitialParameters n (c.seed ρ κ) c.lower c.upper ρ κ c.typeConstant := by
  have ht := threshold5_pos hn c.lower_pos (zero_lt_one.trans c.upper_gt_one)
    hρ hκ (c.typeD hn).constant_pos
  refine ⟨hn, ?_, c.lower_pos, c.lower_lt_one, c.upper_gt_one, hρ, hρ1,
    hκ, hκ1, (c.typeD hn).constant_pos, ?_⟩
  · change (0 : ℝ) < c.seed ρ κ
    rw [c.seed_coe hn hρ hκ]
    exact half_pos ht
  · rw [c.seed_coe hn hρ hκ]
    exact half_lt_self ht

theorem threshold_eq_initial_bound (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    c.threshold ρ κ = Iteration.perturbation n (c.seed ρ κ) 0 := by
  simp only [Iteration.perturbation, delta, decay_zero, c.seed_coe hn hρ hκ,
    threshold, initialPerturbationThreshold]

/-- Initial iteration data constructed by restricting a sufficiently small global perturbation. -/
def initialData (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ σ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (f : AnalyticPhaseFunction n ambient σ) (hρσ : ρ ≤ σ)
    (hf : f.uniformNorm ≤ c.threshold ρ κ) :
    InitialData n c.frequencyDomain (c.seed ρ κ) c.lower c.upper ρ c.typeConstant where
  domain := c.domain
  integrable := H₀
  perturbation := f.restrict c.subset hρσ c.chart.domain_conj
  inverseFrequency := c.inverse
  chart := c.chart
  analytic := c.analytic
  conj := c.conj
  lower := c.derivative_lower
  upper := c.derivative_upper
  bound := by
    rw [← c.threshold_eq_initial_bound hn hρ hκ]
    exact (f.uniformNorm_restrict_le _ _ _).trans hf
  typeD := c.typeD hn

theorem local_result (c : HamiltonianPatch n H₀ ambient) (hn : 0 < n)
    {ρ σ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (f : AnalyticPhaseFunction n ambient σ) (hρσ : ρ ≤ σ)
    (hf : f.uniformNorm ≤ c.threshold ρ κ) :
    LocalKAMResult (c.parameters hn hρ hρ1 hκ hκ1) (c.initialData hn hρ hκ f hρσ hf) :=
  localKAM _ _

theorem exists_common_threshold (s : Finset (HamiltonianPatch n H₀ ambient))
    (hn : 0 < n) {ρ : ℝ≥0} {κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ c ∈ s, M ≤ c.threshold ρ κ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert c s _ ih =>
    obtain ⟨M, hM, hs⟩ := ih
    refine ⟨min M (c.threshold ρ κ), lt_min hM (c.threshold_pos hn hρ hκ), ?_⟩
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hs d hd)

end HamiltonianPatch
end KamProject.Arnold1963

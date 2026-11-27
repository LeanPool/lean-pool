/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolPartitionQuery
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite pools and finite-horizon limits

The Hilbert-space average of the query indicators represents the actual
fraction of a finite pool that is eventually queried.  Its distance to the
fixed weak limit bounds the corresponding L1 error.  A union bound controls
the high-set mass on which a nonempty pool is not completely queried.

For each fixed pool, the finite-horizon high missed mass and the expected
read fraction converge to their eventual counterparts.  These are actual
query events and supply the analytic limits needed by the finite search.
-/

@[expose] public section

noncomputable section

namespace Klr.Pool

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The Hilbert-space average of the actual eventual-query indicators. -/
def averageL2 (π : ScanRule) (G : Finset ℕ) : Lp ℝ 2 fairCoin :=
  (G.card : ℝ)⁻¹ • ∑ a ∈ G, queryL2 π a

theorem averageL2_coeFn (π : ScanRule) (G : Finset ℕ) :
    averageL2 π G =ᵐ[fairCoin] PoolQuery.readFraction π G := by
  have hsum := Lp.coeFn_finsetSum G (queryL2 π)
  have hind := (eventually_all_finset G).mpr (fun a _ => queryL2_coeFn π a)
  filter_upwards [Lp.coeFn_smul (G.card : ℝ)⁻¹ (∑ a ∈ G, queryL2 π a), hsum, hind]
    with Z hsmul hsum hind
  change ((G.card : ℝ)⁻¹ • ∑ a ∈ G, queryL2 π a) Z = _
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul, hsum, Finset.sum_apply]
  rw [Finset.sum_congr rfl hind]
  simp only [PoolQuery.readFraction, div_eq_mul_inv, mul_comm]

/-- On a probability space, the L1 norm is bounded by the L2 norm. -/
theorem integral_norm_le_L2_norm (f : Lp ℝ 2 fairCoin) :
    (∫ Z, ‖f Z‖ ∂fairCoin) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_eNorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f), Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

namespace QueryPartition

/-- Hilbert-space approximation of a pool gives L1 approximation to the fixed
everywhere bounded Borel representative. -/
theorem integral_abs_readFraction_sub_representative_le
    {π : ℕ → ScanRule} {a : ℕ → ℕ} (D : QueryPartition π a)
    (i : ℕ) (G : Finset ℕ) :
    (∫ Z, |PoolQuery.readFraction (π i) G Z - D.representative i Z| ∂fairCoin) ≤
      ‖averageL2 (π i) G - D.limit i‖ := by
  calc
    _ = ∫ Z, ‖(averageL2 (π i) G - D.limit i) Z‖ ∂fairCoin := by
      apply integral_congr_ae
      filter_upwards [averageL2_coeFn (π i) G, D.representative_ae_eq i,
        Lp.coeFn_sub (averageL2 (π i) G) (D.limit i)] with Z hav hrep hsub
      simp only [Pi.sub_apply] at hsub
      rw [hsub, hav, hrep, Real.norm_eq_abs]
    _ ≤ _ := integral_norm_le_L2_norm _

end QueryPartition

end Klr.Pool

namespace Klr.PoolQuery

open MeasureTheory Filter
open scoped Topology BigOperators symmDiff

/-- If all members of a nonempty pool are eventually queried, its eventual
read fraction is one. -/
theorem readFraction_eq_one_of_forall_reads (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) {Z : Cantor} (hreads : ∀ a ∈ G, Reads π a Z) :
    readFraction π G Z = 1 := by
  classical
  have hs : ∑ a ∈ G, indicator π a Z = (G.card : ℝ) := by
    calc
      _ = ∑ _a ∈ G, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [indicator, hreads a ha]
      _ = _ := by simp
  rw [readFraction, hs]
  exact div_self (by exact_mod_cast hG.card_ne_zero)

/-- The high-set mass missing any member of a nonempty pool is bounded by
the sum of its individual missed masses. -/
theorem high_miss_le_sum (π : ScanRule) {G : Finset ℕ} (hG : G.Nonempty)
    (H : Set Cantor) :
    fairCoin.real {Z | Z ∈ H ∧ readFraction π G Z < 1} ≤
      ∑ a ∈ G, fairCoin.real (H \ {Z | Reads π a Z}) := by
  have hsub : {Z | Z ∈ H ∧ readFraction π G Z < 1} ⊆
      ⋃ a ∈ G, H \ {Z | Reads π a Z} := by
    intro Z hZ
    by_contra hnot
    have hall : ∀ a ∈ G, Reads π a Z := by
      intro a ha
      by_contra hmiss
      exact hnot (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hZ.1, hmiss⟩⟩)
    have hone := readFraction_eq_one_of_forall_reads π hG hall
    exact (ne_of_lt hZ.2) hone
  exact (measureReal_mono hsub (measure_ne_top fairCoin _)).trans
    (measureReal_biUnion_finset_le G _)

/-- Replacing the fixed high set by a finite-prefix approximation costs only
its symmetric-difference error. -/
theorem high_miss_le_sum_add_symmDiff (π : ScanRule) {G : Finset ℕ}
    (hG : G.Nonempty) (H H' : Set Cantor) :
    fairCoin.real {Z | Z ∈ H' ∧ readFraction π G Z < 1} ≤
      (∑ a ∈ G, fairCoin.real (H \ {Z | Reads π a Z})) + fairCoin.real (H' ∆ H) := by
  have hsub : {Z | Z ∈ H' ∧ readFraction π G Z < 1} ⊆
      {Z | Z ∈ H ∧ readFraction π G Z < 1} ∪ (H' ∆ H) := by
    intro Z hZ
    by_cases hz : Z ∈ H
    · exact Or.inl ⟨hz, hZ.2⟩
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hZ.1, hz⟩))
  calc
    _ ≤ fairCoin.real ({Z | Z ∈ H ∧ readFraction π G Z < 1} ∪ (H' ∆ H)) :=
      measureReal_mono hsub (measure_ne_top fairCoin _)
    _ ≤ fairCoin.real {Z | Z ∈ H ∧ readFraction π G Z < 1} + fairCoin.real (H' ∆ H) :=
      measureReal_union_le _ _
    _ ≤ _ := by linarith [high_miss_le_sum π hG H]

/-- The actual finite-time high missed mass converges to the eventual high
missed mass of the same fixed pool. -/
theorem tendsto_high_missBy (π : ScanRule) (G : Finset ℕ)
    {H : Set Cantor} (hH : MeasurableSet H) :
    Tendsto
      (fun V : ℕ => fairCoin.real {Z | Z ∈ H ∧ readFractionBy π G V Z < 1})
      atTop (𝓝 (fairCoin.real {Z | Z ∈ H ∧ readFraction π G Z < 1})) := by
  classical
  let S (V : ℕ) : Set Cantor := {Z | Z ∈ H ∧ readFractionBy π G V Z < 1}
  let T : Set Cantor := {Z | Z ∈ H ∧ readFraction π G Z < 1}
  have hS (V : ℕ) : MeasurableSet (S V) :=
    hH.inter (measurableSet_lt (measurable_readFractionBy π G V) measurable_const)
  have hT : MeasurableSet T :=
    hH.inter (measurableSet_lt (measurable_readFraction π G) measurable_const)
  have h := tendsto_integral_of_dominated_convergence (μ := fairCoin)
    (F := fun V => (S V).indicator (fun _ => (1 : ℝ)))
    (f := T.indicator (fun _ => (1 : ℝ))) (fun _ => (1 : ℝ))
    (fun V => (measurable_const.indicator (hS V)).aestronglyMeasurable)
    (integrable_const 1) (fun V => Filter.Eventually.of_forall fun Z => by
      by_cases hz : Z ∈ S V <;> simp [Set.indicator, hz])
    (Filter.Eventually.of_forall fun Z => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_readFractionBy_eq π G Z] with V hV
      simp only [S, T, Set.indicator, Set.mem_ofPred, hV])
  have hSI (V : ℕ) : (∫ Z, (S V).indicator (fun _ => (1 : ℝ)) Z ∂fairCoin) =
      fairCoin.real (S V) := by
    simpa using integral_indicator_const (μ := fairCoin) (1 : ℝ) (hS V)
  have hTI : (∫ Z, T.indicator (fun _ => (1 : ℝ)) Z ∂fairCoin) =
      fairCoin.real T := by
    simpa using integral_indicator_const (μ := fairCoin) (1 : ℝ) hT
  simpa only [hSI, hTI] using h

/-- Expected finite-time query fractions converge to the expected eventual
fraction for every fixed finite pool. -/
theorem tendsto_integral_readFractionBy (π : ScanRule) (G : Finset ℕ) :
    Tendsto (fun V : ℕ => ∫ Z, readFractionBy π G V Z ∂fairCoin)
      atTop (𝓝 (∫ Z, readFraction π G Z ∂fairCoin)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun V => (measurable_readFractionBy π G V).aestronglyMeasurable) (integrable_const 1)
  · intro V
    exact Filter.Eventually.of_forall fun Z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (readFractionBy_nonneg π G V Z)]
      exact (readFractionBy_le_readFraction π G V Z).trans (readFraction_le_one π G Z)
  · apply Filter.Eventually.of_forall
    intro Z
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_readFractionBy_eq π G Z] with V hV
    exact hV.symm

/-- Expected eventual coverage is the average of the individual query
probabilities. -/
theorem integral_readFraction (π : ScanRule) (G : Finset ℕ) :
    (∫ Z, readFraction π G Z ∂fairCoin) =
      (∑ a ∈ G, fairCoin.real {Z | Reads π a Z}) / G.card := by
  unfold readFraction
  rw [integral_div, integral_finsetSum G (fun a _ => integrable_indicator π a)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simpa only [indicator, smul_eq_mul, mul_one] using
    integral_indicator_const (μ := fairCoin) (1 : ℝ) (measurableSet_reads π a)

end Klr.PoolQuery

/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.DropEvents
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Summability of actual forced wagers from early and late estimates

For each block, the early contribution is the finite sum of absolute wagers
at that block's actual rank-drop queries before its prescribed horizon.  A
finite sum of the expectations of these contributions makes their total
finite almost surely.  A summable sequence of late-drop probabilities leaves
only finitely many late blocks by Borel–Cantelli; freshness and finite block
supports then leave only finitely many late queries.

The main theorem concludes summability on all actual forced queries.  The
two quantitative hypotheses remain application obligations: this file does
not construct blocks satisfying the paper's stage estimates.  Neither
disjointness of the blocks nor a uniform bound on the wagers is needed for
this implication.
-/

@[expose] public section

namespace Klr.EarlyLateWagers

open MeasureTheory DropEvents
open scoped ENNReal

/-- The absolute wager at a rank drop in one specified block, and zero otherwise. -/
noncomputable def blockWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (j : ℕ) (X : Cantor) (t : ℕ) : ℝ := by
  classical
  exact if atTime B π j X t then |w (π.transcript X t)| else 0

/-- The actual early rank-drop wager mass in block `j`. -/
noncomputable def earlyWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ) (X : Cantor) : ℝ :=
  ∑ t ∈ Finset.range (V j), blockWager B π w j X t

/-- The actual absolute wager series restricted to rank-drop queries. -/
noncomputable def forcedWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (X : Cantor) (t : ℕ) : ℝ := by
  classical
  exact if BlockProductAnswer.forced B π (π.transcript X t)
    then |w (π.transcript X t)| else 0

/-- A query counted once whenever it is early for some block in which it loses rank. -/
noncomputable def earlyPart (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (t : ℕ) : ℝ := by
  classical
  exact if ∃ j, t < V j ∧ atTime B π j X t then |w (π.transcript X t)| else 0

/-- A query counted once whenever it is late for some block in which it loses rank. -/
noncomputable def latePart (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (t : ℕ) : ℝ := by
  classical
  exact if ∃ j, V j ≤ t ∧ atTime B π j X t then |w (π.transcript X t)| else 0

/-- The nonnegative two-index array used to sum early contributions. -/
noncomputable def earlyTerm (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (j t : ℕ) : ℝ≥0∞ := by
  classical
  exact if t < V j ∧ atTime B π j X t then ENNReal.ofReal |w (π.transcript X t)| else 0

theorem blockWager_nonneg (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (j : ℕ) (X : Cantor) (t : ℕ) :
    0 ≤ blockWager B π w j X t := by
  classical
  unfold blockWager
  split_ifs <;> positivity

theorem earlyWager_nonneg (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ) (X : Cantor) :
    0 ≤ earlyWager B π w V j X :=
  Finset.sum_nonneg fun t _ => blockWager_nonneg B π w j X t

theorem earlyPart_nonneg (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (t : ℕ) :
    0 ≤ earlyPart B π w V X t := by
  classical
  unfold earlyPart
  split_ifs <;> positivity

theorem latePart_nonneg (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (t : ℕ) :
    0 ≤ latePart B π w V X t := by
  classical
  unfold latePart
  split_ifs <;> positivity

theorem forcedWager_nonneg (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (X : Cantor) (t : ℕ) :
    0 ≤ forcedWager B π w X t := by
  classical
  unfold forcedWager
  split_ifs <;> positivity

theorem measurable_blockWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (j t : ℕ) :
    Measurable (fun X => blockWager B π w j X t) := by
  classical
  exact measurable_transcript_eval π t
    (fun v => if atBlock B π j v then |w v| else 0)

theorem measurable_earlyWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ) :
    Measurable (earlyWager B π w V j) := by
  exact Finset.measurable_fun_sum _ fun t _ => measurable_blockWager B π w j t

/-- A normalized strategy contributes at most one half per early query. -/
theorem earlyWager_le_half_horizon (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (hw : ∀ v, |w v| ≤ (1 / 2 : ℝ))
    (j : ℕ) (X : Cantor) : earlyWager B π w V j X ≤ (V j : ℝ) / 2 := by
  classical
  calc
    earlyWager B π w V j X ≤ ∑ _t ∈ Finset.range (V j), (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      unfold blockWager
      split_ifs
      · exact hw _
      · norm_num
    _ = (V j : ℝ) / 2 := by simp [div_eq_mul_inv]

/-- The finite-horizon bound also controls its lower Lebesgue integral. -/
theorem lintegral_earlyWager_le (μ : Measure Cantor) (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (hw : ∀ v, |w v| ≤ (1 / 2 : ℝ)) (j : ℕ) :
    (∫⁻ X, ENNReal.ofReal (earlyWager B π w V j X) ∂μ) ≤
      ENNReal.ofReal ((V j : ℝ) / 2) * μ Set.univ := by
  calc
    _ ≤ ∫⁻ _X : Cantor, ENNReal.ofReal ((V j : ℝ) / 2) ∂μ :=
      lintegral_mono fun X => ENNReal.ofReal_le_ofReal (earlyWager_le_half_horizon B π w V hw j X)
    _ = _ := lintegral_const _

/-- Initial finitely many blocks have finite early expectation under every finite law. -/
theorem lintegral_earlyWager_lt_top (μ : Measure Cantor) [IsFiniteMeasure μ]
    (B : ℕ → AffineBlock) (π : ScanRule) (w : List Bool → ℝ) (V : ℕ → ℕ)
    (hw : ∀ v, |w v| ≤ (1 / 2 : ℝ)) (j : ℕ) :
    (∫⁻ X, ENNReal.ofReal (earlyWager B π w V j X) ∂μ) < ∞ :=
  lt_of_le_of_lt (lintegral_earlyWager_le μ B π w V hw j)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ))

/-- The inner series is precisely the prescribed finite early contribution. -/
theorem tsum_earlyTerm (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (j : ℕ) :
    ∑' t, earlyTerm B π w V X j t = ENNReal.ofReal (earlyWager B π w V j X) := by
  classical
  rw [tsum_eq_sum (s := Finset.range (V j)) (fun t ht => by
    simp only [Finset.mem_range] at ht
    simp [earlyTerm, ht])]
  rw [earlyWager, ENNReal.ofReal_sum_of_nonneg
    (fun t _ => blockWager_nonneg B π w j X t)]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  by_cases hd : atTime B π j X t <;> simp [earlyTerm, blockWager, ht', hd]

/-- Counting a query once costs no more than summing its contributions over all blocks. -/
theorem earlyPart_le_tsum (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (t : ℕ) :
    ENNReal.ofReal (earlyPart B π w V X t) ≤ ∑' j, earlyTerm B π w V X j t := by
  classical
  by_cases h : ∃ j, t < V j ∧ atTime B π j X t
  · obtain ⟨j, hj⟩ := h
    rw [earlyPart, ite_eq_left ⟨j, hj⟩]
    calc
      ENNReal.ofReal |w (π.transcript X t)| = earlyTerm B π w V X j t := by
        simp [earlyTerm, hj]
      _ ≤ ∑' k, earlyTerm B π w V X k t :=
        le_tsum (fun k => earlyTerm B π w V X k t) j
  · simp [earlyPart, h]

/-- Finite total early block mass implies summability of the actual early query series. -/
theorem summable_earlyPart (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor)
    (h : (∑' j, ENNReal.ofReal (earlyWager B π w V j X)) < ∞) :
    Summable (earlyPart B π w V X) := by
  have hle : (∑' t, ENNReal.ofReal (earlyPart B π w V X t)) ≤
      ∑' j, ENNReal.ofReal (earlyWager B π w V j X) := by
    calc
      _ ≤ ∑' t, ∑' j, earlyTerm B π w V X j t :=
        tsum_le_tsum fun t => earlyPart_le_tsum B π w V X t
      _ = ∑' j, ∑' t, earlyTerm B π w V X j t := tsum_comm
      _ = _ := by simp only [tsum_earlyTerm]
  have hs := ENNReal.summable_toReal (lt_of_le_of_lt hle h).ne
  simpa only [ENNReal.toReal_ofReal (earlyPart_nonneg B π w V X _)] using hs

/-- Finitely many late blocks give finitely many actual late queries. -/
theorem finite_late_times (B : ℕ → AffineBlock) (π : ScanRule)
    (V : ℕ → ℕ) (X : Cantor) (h : {j | X ∈ lateEvent B π V j}.Finite) :
    {t | ∃ j, V j ≤ t ∧ atTime B π j X t}.Finite := by
  have hf := h.biUnion (fun j _ => finite_drop_times B π j X)
  apply hf.subset
  rintro t ⟨j, hj, hd⟩
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨⟨t, hj, hd⟩, hd⟩⟩

theorem summable_latePart (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor)
    (h : {j | X ∈ lateEvent B π V j}.Finite) :
    Summable (latePart B π w V X) := by
  classical
  let S := (finite_late_times B π V X h).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro t ht
  have hn : ¬∃ j, V j ≤ t ∧ atTime B π j X t := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ht
  simp [latePart, hn]

theorem forcedWager_le_parts (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (X : Cantor) (t : ℕ) :
    forcedWager B π w X t ≤ earlyPart B π w V X t + latePart B π w V X t := by
  classical
  by_cases h : BlockProductAnswer.forced B π (π.transcript X t)
  · obtain ⟨j, hj⟩ := (forced_iff B π _).mp h
    change atTime B π j X t at hj
    rw [forcedWager, ite_eq_left h]
    by_cases ht : t < V j
    · have he : earlyPart B π w V X t = |w (π.transcript X t)| := by
        exact ite_eq_left (show ∃ k, t < V k ∧ atTime B π k X t from ⟨j, ht, hj⟩)
      rw [he]
      exact le_add_of_nonneg_right (latePart_nonneg B π w V X t)
    · have hl : latePart B π w V X t = |w (π.transcript X t)| := by
        exact ite_eq_left
          (show ∃ k, V k ≤ t ∧ atTime B π k X t from ⟨j, Nat.le_of_not_gt ht, hj⟩)
      rw [hl]
      exact le_add_of_nonneg_left (earlyPart_nonneg B π w V X t)
  · rw [forcedWager, ite_eq_right h]
    exact add_nonneg (earlyPart_nonneg B π w V X t) (latePart_nonneg B π w V X t)

/-- Finite summed expectations imply almost-sure finiteness of total early block mass. -/
theorem ae_early_total_lt_top (μ : Measure Cantor) (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ)
    (h : (∑' j, ∫⁻ X, ENNReal.ofReal (earlyWager B π w V j X) ∂μ) < ∞) :
    ∀ᵐ X ∂μ, (∑' j, ENNReal.ofReal (earlyWager B π w V j X)) < ∞ := by
  have hm : ∀ j, Measurable (fun X => ENNReal.ofReal (earlyWager B π w V j X)) :=
    fun j => (measurable_earlyWager B π w V j).ennreal_ofReal
  apply ae_lt_top (Measurable.tsum hm)
  rw [lintegral_tsum (fun j => (hm j).aemeasurable)]
  exact h.ne

/-- The paper's forced-wager summability conclusion from concrete early/late estimates.
All queries and weights in the hypotheses and conclusion refer to the actual scan path. -/
theorem ae_summable_forcedWager (μ : Measure Cantor) (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ)
    (hlate : (∑' j, μ (lateEvent B π V j)) < ∞)
    (hearly : (∑' j, ∫⁻ X, ENNReal.ofReal (earlyWager B π w V j X) ∂μ) < ∞) :
    ∀ᵐ X ∂μ, Summable (forcedWager B π w X) := by
  filter_upwards [ae_finite_setOfPred_mem hlate.ne,
    ae_early_total_lt_top μ B π w V hearly] with X hXlate hXearly
  apply Summable.of_nonneg_of_le (forcedWager_nonneg B π w X)
    (forcedWager_le_parts B π w V X)
  exact (summable_earlyPart B π w V X hXearly).add (summable_latePart B π w V X hXlate)

/-- No estimates at all are required to sum the contribution of a single fixed block. -/
theorem summable_blockWager (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (j : ℕ) (X : Cantor) : Summable (blockWager B π w j X) := by
  classical
  let S := (finite_drop_times B π j X).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro t ht
  have hn : ¬atTime B π j X t := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using ht
  simp [blockWager, hn]

/-- Deleting finitely many blocks does not change forced-wager summability. -/
theorem summable_forcedWager_of_tail (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (X : Cantor) (J : ℕ)
    (h : Summable (forcedWager (fun j => B (j + J)) π w X)) :
    Summable (forcedWager B π w X) := by
  classical
  have hp : Summable (fun t => ∑ j ∈ Finset.range J, blockWager B π w j X t) :=
    summable_sum (fun j _ => summable_blockWager B π w j X)
  apply Summable.of_nonneg_of_le (forcedWager_nonneg B π w X) _ (hp.add h)
  intro t
  change forcedWager B π w X t ≤
    (∑ j ∈ Finset.range J, blockWager B π w j X t) +
      forcedWager (fun j => B (j + J)) π w X t
  have hprefix : 0 ≤ ∑ j ∈ Finset.range J, blockWager B π w j X t :=
    Finset.sum_nonneg fun j _ => blockWager_nonneg B π w j X t
  by_cases hf : BlockProductAnswer.forced B π (π.transcript X t)
  · obtain ⟨j, hj⟩ := (forced_iff B π _).mp hf
    change atTime B π j X t at hj
    rw [forcedWager, ite_eq_left hf]
    by_cases hlt : j < J
    · have hterm : |w (π.transcript X t)| ≤
          ∑ k ∈ Finset.range J, blockWager B π w k X t := by
        have hle := Finset.single_le_sum (fun k _ => blockWager_nonneg B π w k X t)
          (Finset.mem_range.mpr hlt)
        simpa only [blockWager, ite_eq_left hj] using hle
      exact hterm.trans (le_add_of_nonneg_right
        (forcedWager_nonneg (fun j => B (j + J)) π w X t))
    · have hge := Nat.le_of_not_gt hlt
      have htail : BlockProductAnswer.forced (fun k => B (k + J)) π (π.transcript X t) := by
        refine ⟨j - J, ?_⟩
        simpa only [atTime, atBlock, Nat.sub_add_cancel hge] using hj
      rw [forcedWager, ite_eq_left htail]
      exact le_add_of_nonneg_left hprefix
  · rw [forcedWager, ite_eq_right hf]
    exact add_nonneg hprefix (forcedWager_nonneg (fun j => B (j + J)) π w X t)

/-- The concrete early/late estimates need only hold beyond any fixed block index.
The exceptional blocks are handled pathwise by freshness, without moment hypotheses. -/
theorem ae_summable_forcedWager_tail (μ : Measure Cantor) (B : ℕ → AffineBlock)
    (π : ScanRule) (w : List Bool → ℝ) (V : ℕ → ℕ) (J : ℕ)
    (hlate : (∑' j, μ (lateEvent B π V (j + J))) < ∞)
    (hearly : (∑' j, ∫⁻ X, ENNReal.ofReal (earlyWager B π w V (j + J) X) ∂μ) < ∞) :
    ∀ᵐ X ∂μ, Summable (forcedWager B π w X) := by
  have ht := ae_summable_forcedWager μ (fun j => B (j + J)) π w
    (fun j => V (j + J)) hlate hearly
  filter_upwards [ht] with X hX
  exact summable_forcedWager_of_tail B π w X J hX

/-- Summable numerical majorants for all sufficiently late blocks imply the actual
forced-wager conclusion.  No estimate on the exceptional initial blocks is needed. -/
theorem ae_summable_forcedWager_of_bounds (μ : Measure Cantor) (B : ℕ → AffineBlock)
    (π : ScanRule) (w : List Bool → ℝ) (V : ℕ → ℕ) (J : ℕ)
    (a b : ℕ → ℝ≥0∞) (ha : (∑' j, a j) < ∞) (hb : (∑' j, b j) < ∞)
    (hlate : ∀ j, J ≤ j → μ (lateEvent B π V j) ≤ a j)
    (hearly : ∀ j, J ≤ j →
      (∫⁻ X, ENNReal.ofReal (earlyWager B π w V j X) ∂μ) ≤ b j) :
    ∀ᵐ X ∂μ, Summable (forcedWager B π w X) := by
  apply ae_summable_forcedWager_tail μ B π w V J
  · calc
      (∑' j, μ (lateEvent B π V (j + J))) ≤ ∑' j, a (j + J) :=
        tsum_le_tsum fun j => hlate (j + J) (Nat.le_add_left _ _)
      _ ≤ ∑' j, a j :=
        tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h) a
      _ < ∞ := ha
  · calc
      (∑' j, ∫⁻ X, ENNReal.ofReal (earlyWager B π w V (j + J) X) ∂μ) ≤
          ∑' j, b (j + J) :=
        tsum_le_tsum fun j => hearly (j + J) (Nat.le_add_left _ _)
      _ ≤ ∑' j, b j :=
        tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h) b
      _ < ∞ := hb

end Klr.EarlyLateWagers

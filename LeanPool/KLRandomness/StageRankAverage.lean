/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageRank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Averaging the actual rank-drop events over the candidate list

The finite verifier controls the number of failing candidates separately on
each answer sequence with a dense never-read mask. Integrating that count
gives an average of the actual Borel rank-drop probabilities. This order of
quantifiers permits later simultaneous selection for several scans.
-/

@[expose] public section

noncomputable section

namespace Klr.StageRank

open MeasureTheory SparseListSearch SparseListWeights SparseSearch SparseListCode PoolQuery
open scoped BigOperators

/-- The exact missed count is a measurable real-valued function. -/
theorem measurable_missedCount_real (π : ScanRule) (G : Finset ℕ) :
    Measurable (fun Z => (missedCount π G Z : ℝ)) := by
  have he : (fun Z => (missedCount π G Z : ℝ)) =
      fun Z => (G.card : ℝ) - ∑ a ∈ G, indicator π a Z := by
    funext Z
    have h := sum_indicator_add_missedCount π G Z
    linarith
  rw [he]
  exact measurable_const.sub (Finset.measurable_sum G fun a _ => measurable_indicator π a)

open Classical in
/-- A pointwise count bound outside one exceptional event integrates to a
bound for the sum of the actual event probabilities. -/
theorem sum_measureReal_le_of_card {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (E : Set Ω) (hE : MeasurableSet E)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ x ∉ E,
      ((Finset.univ.filter fun i => x ∈ A i).card : ℝ) ≤ C) :
    (∑ i, μ.real (A i)) ≤ (Fintype.card ι : ℝ) * μ.real E + C := by
  classical
  let f (i : ι) := (A i).indicator (fun _ => (1 : ℝ))
  have hf : ∀ i, Integrable (f i) μ := fun i => (integrable_const 1).indicator (hA i)
  have hg : Integrable (fun x => E.indicator (fun _ => (Fintype.card ι : ℝ)) x + C) μ :=
    ((integrable_const _).indicator hE).add (integrable_const _)
  have hpoint : ∀ x, (∑ i, f i x) ≤
      E.indicator (fun _ => (Fintype.card ι : ℝ)) x + C := by
    intro x
    have hsum : (∑ i, f i x) =
        ((Finset.univ.filter fun i => x ∈ A i).card : ℝ) := by
      simp [f, Set.indicator_apply]
    rw [hsum]
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      apply le_trans _ (le_add_of_nonneg_right hC)
      exact_mod_cast (Finset.card_filter_le (s := Finset.univ) (fun i => x ∈ A i))
    · simpa only [Set.indicator_of_notMem hx, zero_add] using hcount x hx
  calc
    (∑ i, μ.real (A i)) = ∫ x, ∑ i, f i x ∂μ := by
      rw [integral_finsetSum Finset.univ (fun i _ => hf i)]
      simp [f, integral_indicator_const, hA]
    _ ≤ ∫ x, E.indicator (fun _ => (Fintype.card ι : ℝ)) x + C ∂μ :=
      integral_mono (integrable_finsetSum _ (fun i _ => hf i)) hg hpoint
    _ = (Fintype.card ι : ℝ) * μ.real E + C := by
      rw [integral_add ((integrable_const _).indicator hE) (integrable_const _)]
      simp [hE, mul_comm]

/-- The low-part average rank-drop probability of the actual checked list
is at most the low pool exception plus the verifier's bad-rank fraction. -/
theorem average_measureReal_low_hasDrop_le
    {M m r J : ℕ} {τ θ : ℚ} {L : CodeList}
    (hL : Good M m r J τ θ L) (hJ : 0 < J) (hθ : 0 ≤ θ)
    (e : Fin M → ℕ) (he : Function.Injective e)
    (y : Fin L.length → Fin r → ZMod 2)
    (π : ScanRule) (Low : Set Cantor) (hLow : MeasurableSet Low)
    (η : ℝ)
    (hpool : fairCoin.real {Z | Z ∈ Low ∧
      (missedCount π (Finset.univ.image e) Z : ℝ) < (τ : ℝ) * M} ≤ η) :
    (∑ j : Fin L.length, fairCoin.real
      (Low ∩ (NoDrop.noDropTranscripts (listBlock hL e he y j) π)ᶜ)) / J ≤
      η + (θ : ℝ) := by
  classical
  let A (j : Fin L.length) :=
    Low ∩ (NoDrop.noDropTranscripts (listBlock hL e he y j) π)ᶜ
  let E := {Z | Z ∈ Low ∧
    (missedCount π (Finset.univ.image e) Z : ℝ) < (τ : ℝ) * M}
  have hA : ∀ j, MeasurableSet (A j) := fun j =>
    hLow.inter (NoDrop.measurableSet_noDropTranscripts _ _).compl
  have hE : MeasurableSet E :=
    hLow.inter (measurableSet_lt (measurable_missedCount_real π _) measurable_const)
  have hcount : ∀ Z ∉ E,
      ((Finset.univ.filter fun j => Z ∈ A j).card : ℝ) ≤ (θ : ℝ) * J := by
    intro Z hZE
    by_cases hZL : Z ∈ Low
    · have hden : (τ : ℝ) * M ≤ (missedCount π (Finset.univ.image e) Z : ℝ) :=
        not_lt.mp (fun h => hZE ⟨hZL, h⟩)
      have hden' : τ * (M : ℚ) ≤ ((neverRead e π Z).card : ℚ) := by
        rw [card_neverRead e he π Z]
        exact_mod_cast hden
      have hbad :
          ((Finset.univ.filter fun j : Fin L.length =>
            Z ∉ NoDrop.noDropTranscripts (listBlock hL e he y j) π).card : ℝ) ≤
          (θ : ℝ) * J := by
        exact_mod_cast card_hasDrop_le hL e he y π Z hden'
      apply le_trans _ hbad
      exact_mod_cast (Finset.card_le_card (show
        (Finset.univ.filter fun j => Z ∈ A j) ⊆
          (Finset.univ.filter fun j : Fin L.length =>
            Z ∉ NoDrop.noDropTranscripts (listBlock hL e he y j) π) from by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.2⟩))
    · have hzero : (Finset.univ.filter fun j => Z ∈ A j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j _ hj
        exact hZL hj.1
      rw [hzero, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (by exact_mod_cast hθ) (Nat.cast_nonneg _)
  have hsum := sum_measureReal_le_of_card fairCoin A hA E hE ((θ : ℝ) * J)
    (mul_nonneg (by exact_mod_cast hθ) (Nat.cast_nonneg _)) (fun Z hZE => by
      convert hcount Z hZE using 1
      congr 2
      ext j
      simp)
  have hsum' : (∑ j, fairCoin.real (A j)) ≤ (J : ℝ) * η + (θ : ℝ) * J := by
    calc
      _ ≤ (J : ℝ) * fairCoin.real E + (θ : ℝ) * J := by
        simpa only [Fintype.card_fin, hL.1] using hsum
      _ ≤ _ := by
        exact add_le_add (mul_le_mul_of_nonneg_left hpool (Nat.cast_nonneg J)) le_rfl
  apply (div_le_iff₀ (by exact_mod_cast hJ : (0 : ℝ) < J)).mpr
  calc
    _ ≤ (J : ℝ) * η + (θ : ℝ) * J := hsum'
    _ = (η + (θ : ℝ)) * J := by ring

end Klr.StageRank

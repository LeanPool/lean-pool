/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BlockProduct
public import LeanPool.KLRandomness.EarlyLateWagers
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Measurability

/-!
# Finite-horizon expectations under the infinite block law

If every block not yet imposed has full unread rank after every transcript of a
fixed length, the infinite block law has exactly the same finite-answer
distribution as the current finite stage.  Consequently every functional of
those answers has the same expectation under the two laws.

The final theorem applies this equality to the early rank-drop wager sum in
Section 6.  Its horizon dependence is proved directly from the definitions; no
distributional or expectation-transfer premise is assumed.
-/

@[expose] public section

namespace Klr.HorizonLaw

open MeasureTheory StoppingTranscript
open scoped ENNReal

/-- The finite answer vector of a total scan, with a fixed finite codomain. -/
def prefixAnswers (π : ScanRule) (N : ℕ) (X : Cantor) : Fin N → Bool :=
  fun i => (π.transcript X N).getD i.val false

theorem measurable_prefixAnswers (π : ScanRule) (N : ℕ) :
    Measurable (prefixAnswers π N) :=
  Measurable.of_eval fun i =>
    DropEvents.measurable_transcript_eval π N (fun v => v.getD i.val false)

@[simp] theorem ofFn_prefixAnswers (π : ScanRule) (N : ℕ) (X : Cantor) :
    List.ofFn (prefixAnswers π N X) = π.transcript X N := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_ofFn, prefixAnswers]
  exact List.getD_eq_getElem _ _ hj

theorem prefixAnswers_preimage_singleton (π : ScanRule) (N : ℕ)
    (a : Fin N → Bool) :
    prefixAnswers π N ⁻¹' {a} = inputEvent π (List.ofFn a) := by
  ext X
  change prefixAnswers π N X = a ↔
    π.transcript X (List.ofFn a).length = List.ofFn a
  rw [List.length_ofFn, ← ofFn_prefixAnswers π N X, List.ofFn_inj]

/-- Equality of the complete finite-answer distributions. -/
theorem map_prefixAnswers_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v) :
    (BlockProduct.law B hdis).map (prefixAnswers π N) =
      (PrefixStage.law B n).map (prefixAnswers π N) := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_prefixAnswers π N) (measurableSet_singleton a),
    Measure.map_apply (measurable_prefixAnswers π N) (measurableSet_singleton a),
    prefixAnswers_preimage_singleton]
  exact BlockProduct.law_inputEvent_eq_of_fullRank B hdis n π (List.ofFn a)
    (hfull _ List.length_ofFn)

/-- Every nonnegative functional of the finite answer vector has the same integral. -/
theorem lintegral_prefixAnswers_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v)
    (f : (Fin N → Bool) → ℝ≥0∞) :
    ∫⁻ X, f (prefixAnswers π N X) ∂BlockProduct.law B hdis =
      ∫⁻ X, f (prefixAnswers π N X) ∂PrefixStage.law B n := by
  rw [← lintegral_map (measurable_of_countable f) (measurable_prefixAnswers π N),
    ← lintegral_map (measurable_of_countable f) (measurable_prefixAnswers π N),
    map_prefixAnswers_eq_stage B hdis n π N hfull]

/-- The corresponding real-valued integral identity. -/
theorem integral_prefixAnswers_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v)
    (f : (Fin N → Bool) → ℝ) :
    ∫ X, f (prefixAnswers π N X) ∂BlockProduct.law B hdis =
      ∫ X, f (prefixAnswers π N X) ∂PrefixStage.law B n := by
  rw [← integral_map_of_stronglyMeasurable (measurable_prefixAnswers π N)
      (StronglyMeasurable.of_discrete (f := f)),
    ← integral_map_of_stronglyMeasurable (measurable_prefixAnswers π N)
      (StronglyMeasurable.of_discrete (f := f)),
    map_prefixAnswers_eq_stage B hdis n π N hfull]

/-- A word functional needs no independent measurability assumption: only finitely
many length-`N` words can occur. -/
theorem lintegral_transcript_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v)
    (f : List Bool → ℝ≥0∞) :
    ∫⁻ X, f (π.transcript X N) ∂BlockProduct.law B hdis =
      ∫⁻ X, f (π.transcript X N) ∂PrefixStage.law B n := by
  simpa only [ofFn_prefixAnswers] using
    lintegral_prefixAnswers_eq_stage B hdis n π N hfull (fun a => f (List.ofFn a))

theorem integral_transcript_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v)
    (f : List Bool → ℝ) :
    ∫ X, f (π.transcript X N) ∂BlockProduct.law B hdis =
      ∫ X, f (π.transcript X N) ∂PrefixStage.law B n := by
  simpa only [ofFn_prefixAnswers] using
    integral_prefixAnswers_eq_stage B hdis n π N hfull (fun a => f (List.ofFn a))

/-- Any function constant on equal horizon transcripts factors through the finite
answer vector, including values on unrealizable words. -/
theorem factorsThrough_prefixAnswers {α : Type*} (π : ScanRule) (N : ℕ)
    (g : Cantor → α)
    (hg : ∀ X Y, π.transcript X N = π.transcript Y N → g X = g Y) :
    Function.FactorsThrough g (prefixAnswers π N) := by
  intro X Y h
  apply hg X Y
  simpa only [ofFn_prefixAnswers] using congrArg List.ofFn h

/-- Equality of nonnegative integrals for any horizon-dependent input functional. -/
theorem lintegral_eq_stage_of_transcript (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v)
    (g : Cantor → ℝ≥0∞)
    (hg : ∀ X Y, π.transcript X N = π.transcript Y N → g X = g Y) :
    ∫⁻ X, g X ∂BlockProduct.law B hdis =
      ∫⁻ X, g X ∂PrefixStage.law B n := by
  obtain ⟨f, rfl⟩ := (Function.factorsThrough_iff g).mp
    (factorsThrough_prefixAnswers π N g hg)
  exact lintegral_prefixAnswers_eq_stage B hdis n π N hfull f

theorem integral_eq_stage_of_transcript (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (n : ℕ) (π : ScanRule) (N : ℕ)
    (hfull : ∀ v, v.length = N → ∀ k, n ≤ k → (B k).UnreadFullRank π v)
    (g : Cantor → ℝ)
    (hg : ∀ X Y, π.transcript X N = π.transcript Y N → g X = g Y) :
    ∫ X, g X ∂BlockProduct.law B hdis =
      ∫ X, g X ∂PrefixStage.law B n := by
  obtain ⟨f, rfl⟩ := (Function.factorsThrough_iff g).mp
    (factorsThrough_prefixAnswers π N g hg)
  exact integral_prefixAnswers_eq_stage B hdis n π N hfull f

/-- The early wager sum is determined by the transcript at its prescribed horizon. -/
theorem earlyWager_eq_of_transcript (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ) (X Y : Cantor)
    (h : π.transcript X (V j) = π.transcript Y (V j)) :
    EarlyLateWagers.earlyWager B π w V j X =
      EarlyLateWagers.earlyWager B π w V j Y := by
  classical
  unfold EarlyLateWagers.earlyWager
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t ≤ V j := (Finset.mem_range.mp ht).le
  have he : π.transcript X t = π.transcript Y t := by
    calc
      π.transcript X t = (π.transcript X (V j)).take t :=
        (π.transcript_take X ht').symm
      _ = (π.transcript Y (V j)).take t := congrArg (List.take t) h
      _ = π.transcript Y t := π.transcript_take Y ht'
  simp only [EarlyLateWagers.blockWager, DropEvents.atTime, he]
  rfl

/-- The early expectation under the actual infinite law is exactly the expectation
after imposing block `j`, provided all later blocks preserve full rank through `V j`. -/
theorem lintegral_earlyWager_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ)
    (havoid : ∀ v, v.length = V j → ∀ k, j < k → (B k).UnreadFullRank π v) :
    ∫⁻ X, ENNReal.ofReal (EarlyLateWagers.earlyWager B π w V j X)
        ∂BlockProduct.law B hdis =
      ∫⁻ X, ENNReal.ofReal (EarlyLateWagers.earlyWager B π w V j X)
        ∂PrefixStage.law B (j + 1) := by
  apply lintegral_eq_stage_of_transcript B hdis (j + 1) π (V j)
    (fun v hv k hk => havoid v hv k (Nat.lt_of_succ_le hk))
  intro X Y h
  exact congrArg ENNReal.ofReal (earlyWager_eq_of_transcript B π w V j X Y h)

theorem integral_earlyWager_eq_stage (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (π : ScanRule) (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ)
    (havoid : ∀ v, v.length = V j → ∀ k, j < k → (B k).UnreadFullRank π v) :
    ∫ X, EarlyLateWagers.earlyWager B π w V j X ∂BlockProduct.law B hdis =
      ∫ X, EarlyLateWagers.earlyWager B π w V j X ∂PrefixStage.law B (j + 1) := by
  exact integral_eq_stage_of_transcript B hdis (j + 1) π (V j)
    (fun v hv k hk => havoid v hv k (Nat.lt_of_succ_le hk)) _
    (earlyWager_eq_of_transcript B π w V j)

end Klr.HorizonLaw

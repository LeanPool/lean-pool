/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageRecursion
public import LeanPool.KLRandomness.StageRationalError

/-!
# Dependent stage recursion preserving coordinate restrictions

Starting from a concrete one-step extension theorem, dependent recursion
builds coherent finite histories. Their diagonal sequence has disjoint
supports, satisfies the actual `StageEstimates` for each eventually protected
strategy, and has a short exact affine program at every test level.

The coordinate invariant is part of the selected extension before classical
choice is applied. Merely proving a stronger existence theorem and then
choosing from the weaker step relation would lose this invariant.
-/

@[expose] public section

noncomputable section

namespace Klr.ConfinedStageRecursion

open MeasureTheory ProbabilityTheory StageRecursion
open scoped ENNReal

/-- A selected actual extension of one finite history. -/
structure Chosen (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
    (A : ℕ → ℕ → Prop) {n : ℕ} (h : History n) where
  /-- The affine block supported in the prescribed coordinates for this stage. -/
  block : AffineBlock
  /-- Finite query horizon established with this block. -/
  horizon : ℕ
  specification : Step s H h.blocks n (h.cutoff s)
    (StageErrorBudget.rational n) block horizon
  confined : ∀ p ∈ block.support, A n p

variable (s : ℕ → BettingStrategy) (H : ℕ → Set Cantor)
  (A : ℕ → ℕ → Prop)
  (hstep : ∀ (old : ℕ → AffineBlock),
    Pairwise (fun i j => Disjoint (old i).support (old j).support) →
    ∀ n z : ℕ, ∃ (C : AffineBlock) (V : ℕ),
      Step s H old n z (StageErrorBudget.rational n) C V ∧
        ∀ p ∈ C.support, A n p)

/-- Choice is used only to assemble the mathematical sequence from the
proved nonempty family of successful finite extensions. -/
def chooseNext {n : ℕ} (h : History n) : Chosen s H A h :=
  Classical.choice (by
    obtain ⟨C, V, hCV, hCA⟩ := hstep h.blocks h.disjoint n (h.cutoff s)
    exact ⟨⟨C, V, hCV, hCA⟩⟩)

/-- The recursively constructed, padded finite history. -/
def histories : (n : ℕ) → History n
  | 0 => History.empty
  | n + 1 =>
    let h := histories n
    let c := chooseNext s H A hstep h
    h.extend s c.block c.horizon c.specification.above

/-- The actual new block selected at each stage. -/
def blocks (n : ℕ) : AffineBlock := (chooseNext s H A hstep (histories s H A hstep n)).block

/-- The common protected-scan horizon selected at each stage. -/
def horizons (n : ℕ) : ℕ := (chooseNext s H A hstep (histories s H A hstep n)).horizon

theorem histories_succ_blocks (n : ℕ) :
    (histories s H A hstep (n + 1)).blocks =
      Function.update (histories s H A hstep n).blocks n (blocks s H A hstep n) := rfl

theorem histories_succ_horizon (n : ℕ) :
    (histories s H A hstep (n + 1)).horizon =
      Function.update (histories s H A hstep n).horizon n (horizons s H A hstep n) := rfl

/-- Every finite history is the exact initial segment of the diagonal blocks. -/
theorem histories_blocks_eq (n j : ℕ) (hj : j < n) :
    (histories s H A hstep n).blocks j = blocks s H A hstep j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [histories_succ_blocks]
    by_cases hjn : j = n
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hjn]
      exact ih (by omega)

/-- The selected horizons have the same coherence property. -/
theorem histories_horizon_eq (n j : ℕ) (hj : j < n) :
    (histories s H A hstep n).horizon j = horizons s H A hstep j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [histories_succ_horizon]
    by_cases hjn : j = n
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hjn]
      exact ih (by omega)

/-- All preceding finite-stage laws agree exactly with the laws of the
diagonal sequence, including laws strictly before the latest history. -/
theorem histories_law_eq (n a : ℕ) (ha : a ≤ n) :
    PrefixStage.law (histories s H A hstep n).blocks a =
      PrefixStage.law (blocks s H A hstep) a := by
  apply congrArg AffineBlock.finiteStageLaw
  funext j
  exact histories_blocks_eq s H A hstep n j.val (lt_of_lt_of_le j.isLt ha)

theorem blocks_pairwise :
    Pairwise (fun i j => Disjoint (blocks s H A hstep i).support
      (blocks s H A hstep j).support) := by
  intro i j hij
  have hi : i < max i j + 1 := Nat.lt_succ_of_le (le_max_left _ _)
  have hj : j < max i j + 1 := Nat.lt_succ_of_le (le_max_right _ _)
  have hd := (histories s H A hstep (max i j + 1)).disjoint hij
  dsimp only at hd
  rwa [histories_blocks_eq s H A hstep _ i hi, histories_blocks_eq s H A hstep _ j hj] at hd

theorem selected_step (n : ℕ) :
    Step s H (histories s H A hstep n).blocks n ((histories s H A hstep n).cutoff s)
      (StageErrorBudget.rational n) (blocks s H A hstep n) (horizons s H A hstep n) :=
  (chooseNext s H A hstep (histories s H A hstep n)).specification

/-- Coordinate restrictions survive the choice of the actual diagonal block. -/
theorem blocks_confined (n : ℕ) :
    ∀ p ∈ (blocks s H A hstep n).support, A n p :=
  (chooseNext s H A hstep (histories s H A hstep n)).confined

/-- The early wager of one block depends only on that block and its horizon. -/
theorem earlyWager_single (B : ℕ → AffineBlock) (π : ScanRule)
    (w : List Bool → ℝ) (V : ℕ → ℕ) (j : ℕ) :
    EarlyLateWagers.earlyWager (fun _ => B j) π w (fun _ => V j) 0 =
      EarlyLateWagers.earlyWager B π w V j := rfl

/-- Later blocks avoid every branch through every earlier protected horizon. -/
theorem horizon_avoidance (i j k : ℕ) (hij : i ≤ j) (hjk : j < k)
    (v : List Bool) (hv : v.length = horizons s H A hstep j) :
    (blocks s H A hstep k).UnreadFullRank (s i).normalize.scan v := by
  apply HorizonAvoidance.unreadFullRank_of_queryBound_le _ _ (horizons s H A hstep j) _ v hv.le
  intro q hq
  have hb := History.queryBound_le_cutoff s (histories s H A hstep k) ⟨j, hjk⟩ i hij
  rw [histories_horizon_eq s H A hstep k j hjk] at hb
  exact hb.trans ((selected_step s H A hstep k).above q hq)

/-- The finite construction yields all actual stage estimates for strategy
`i` from stage `i` onward. -/
theorem stageEstimates (hH : ∀ i, MeasurableSet (H i)) (i : ℕ) :
    StageEstimates (blocks s H A hstep) (s i).normalize.scan
      (s i).normalize.capital.wager (horizons s H A hstep) (H i) i := by
  refine ⟨hH i, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hij v hv k hjk
    exact horizon_avoidance s H A hstep i j k hij hjk v hv
  · intro j hij
    have h := (selected_step s H A hstep j).early_and_partial i hij
    rw [histories_law_eq s H A hstep j j le_rfl,
      ← PrefixStage.law_succ_eq_cond, earlyWager_single] at h
    have hb : ENNReal.ofReal (4 * (StageErrorBudget.rational j : ℝ)) =
        4 * StageErrorBudget.error j := by
      simpa only [Nat.cast_ofNat] using StageErrorBudget.ofReal_mul_rational 4 j
    rwa [hb] at h
  · intro j hij
    have h := (selected_step s H A hstep j).first_drop_tail i hij
    rw [histories_law_eq s H A hstep j j le_rfl,
      ← PrefixStage.law_succ_eq_cond] at h
    have hb : ENNReal.ofReal (2 * (StageErrorBudget.rational j : ℝ)) =
        2 * StageErrorBudget.error j := by
      simpa only [Nat.cast_ofNat] using StageErrorBudget.ofReal_mul_rational 2 j
    rwa [hb] at h
  · intro j hij
    have h := (selected_step s H A hstep j).high_no_drop i hij
    rwa [histories_law_eq s H A hstep j j le_rfl, StageErrorBudget.ofReal_rational] at h
  · intro j hij k hjk
    have h := (selected_step s H A hstep k).earlier_low_drop
      (j + 1) (by omega) i (by omega)
    rwa [histories_law_eq s H A hstep k (j + 1) (by omega),
      StageErrorBudget.ofReal_rational] at h

/-- Stage `n` supplies the exact short affine program required at test level `n`. -/
theorem description (n : ℕ) : ∃ (p : List Bool) (c : AffineCode.Data),
    c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
      AffineCode.rank c = (blocks s H A hstep n).rank ∧
      2 * p.length + n + 1 ≤ AffineCode.rank c ∧
      AffineCode.event c = (blocks s H A hstep n).event :=
  (selected_step s H A hstep n).description

include hstep in
/-- The concrete one-stage extension relation glues to a full sequence
with the probabilistic estimates and exact description obligations discharged. -/
theorem exists_sequence (hH : ∀ i, MeasurableSet (H i)) :
    ∃ (B : ℕ → AffineBlock) (V : ℕ → ℕ),
      Pairwise (fun i j => Disjoint (B i).support (B j).support) ∧
      (∀ n, ∀ p ∈ (B n).support, A n p) ∧
      (∀ i, StageEstimates B (s i).normalize.scan (s i).normalize.capital.wager V (H i) i) ∧
      ∀ n : ℕ, ∃ (p : List Bool) (c : AffineCode.Data),
        c ∈ AffineDescription.run p ∧ AffineCode.valid c = true ∧
          2 * p.length + n + 1 ≤ AffineCode.rank c ∧ AffineCode.event c = (B n).event := by
  refine ⟨blocks s H A hstep, horizons s H A hstep, blocks_pairwise s H A hstep,
    blocks_confined s H A hstep, stageEstimates s H A hstep hH, ?_⟩
  intro n
  obtain ⟨p, c, hp, hc, _, hb, he⟩ := description s H A hstep n
  exact ⟨p, c, hp, hc, hb, he⟩

end Klr.ConfinedStageRecursion

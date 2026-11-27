/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageConditionalScan
public import LeanPool.KLRandomness.StageHorizonChoice
public import LeanPool.KLRandomness.StageRankCode

/-!
# The actual computable finite syndrome objective

This combines the executable support-wager and partial-rank tests with exact
finite conditional integration. For a fixed protected list of strategies,
the whole objective is uniformly computable in the pool, candidate, horizon,
and syndrome. Its values are the conditional integrals used in the analytic
syndrome-choice theorem.
-/

@[expose] public section

noncomputable section

namespace Klr.StageSyndromeObjective

open MeasureTheory ProbabilityTheory SparseSearch SparseListSearch StageCandidate
open StageFiniteWager RationalComputability
open scoped BigOperators

/-- Rational value of the finite objective on one answer transcript. -/
def statistic (s : BettingStrategy) (G : List ℕ) (a : Entry) (v : List Bool) : ℚ :=
  truncatedCandidate s.normalize.scan (StageFiniteWager.normalizedWager s) G a v +
    if StageRankCode.partialTest s.normalize.scan G a.2 v then 1 else 0

theorem computable_statistic (s : BettingStrategy) {α : Type*} [Primcodable α]
    {G : α → List ℕ} {a : α → Entry} {v : α → List Bool}
    (hG : Computable G) (ha : Computable a) (hv : Computable v) :
    Computable (fun p => statistic s (G p) (a p) (v p)) := by
  have ht := computable_normalized_truncatedCandidate s hG ha hv
  have hp := StageRankCode.computable_partialTest s.normalize.scan hG
    (Computable.snd.comp ha) hv
  exact (primrec_rat_add.to_comp.comp ht
    (Computable.cond hp (Computable.const (1 : ℚ)) (Computable.const 0))).of_eq
      fun _ => by simp only [statistic, Bool.cond_eq_ite]

/-- Actual conditional expectation of one strategy's finite objective. -/
def oneCost (s : BettingStrategy) (cs : List AffineCode.Data)
    (G : List ℕ) (a : Entry) (V : ℕ) (y : List Bool) : ℚ :=
  StageConditionalScan.expectation cs G a.2 y s.normalize.scan V (statistic s G a)

theorem computable_oneCost (s : BettingStrategy) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ} {a : α → Entry}
    {V : α → ℕ} {y : α → List Bool}
    (hcs : Computable cs) (hG : Computable G) (ha : Computable a)
    (hV : Computable V) (hy : Computable y) :
    Computable (fun p => oneCost s (cs p) (G p) (a p) (V p) (y p)) :=
  StageConditionalScan.computable_expectation s.normalize.scan hcs hG
    (Computable.snd.comp ha) hy hV
    (computable_statistic s (hG.comp Computable.fst) (ha.comp Computable.fst) Computable.snd).to₂

/-- Sum the exact conditional costs over the fixed protected strategy list. -/
def cost (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (G : List ℕ) (a : Entry) (V : ℕ) (y : List Bool) : ℚ :=
  (rules.map fun s => oneCost s cs G a V y).sum

theorem computable_cost (rules : List BettingStrategy) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ} {a : α → Entry}
    {V : α → ℕ} {y : α → List Bool}
    (hcs : Computable cs) (hG : Computable G) (ha : Computable a)
    (hV : Computable V) (hy : Computable y) :
    Computable (fun p => cost rules (cs p) (G p) (a p) (V p) (y p)) := by
  induction rules with
  | nil => exact Computable.const 0
  | cons s rules ih =>
    exact primrec_rat_add.to_comp.comp (computable_oneCost s hcs hG ha hV hy) ih

theorem statistic_transcript (s : BettingStrategy) (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (z : Fin r → ZMod 2) (V : ℕ) (X : Cantor) :
    (statistic s G a (s.normalize.scan.transcript X V) : ℝ) =
      (truncated s.normalize.scan (StageFiniteWager.normalizedWager s)
        (block G.get hG.injective_get a ha z).support (s.normalize.scan.transcript X V) : ℝ) +
      (LateDropBound.partialEvent (block G.get hG.injective_get a ha z)
        s.normalize.scan V).indicator (fun _ => (1 : ℝ)) X := by
  rw [statistic, Rat.cast_add, truncatedCandidate_eq_block _ _ G hG a ha z]
  congr 1
  have he := StageRankCode.partialTest_eq_true s.normalize.scan G hG a ha z
    (s.normalize.scan.transcript X V)
  change _ ↔ _ at he
  by_cases hx : X ∈ LateDropBound.partialEvent (block G.get hG.injective_get a ha z)
      s.normalize.scan V
  · have ht := he.mpr hx
    simp only [ht, ite_true, Rat.cast_one, Set.indicator_of_mem hx]
  · have ht := mt he.mp hx
    simp only [ht, Bool.false_eq_true, ite_false, Rat.cast_zero, Set.indicator_of_notMem hx]

/-- The finite rational total is exactly the actual syndrome objective. -/
theorem cost_eq_integral (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (V : ℕ) (y : List Bool)
    (z : Fin r → ZMod 2) :
    (cost rules cs G a V y : ℝ) =
      ∫ X, StageHorizonChoice.objective (block G.get hG.injective_get a ha z)
        (fun i : Fin rules.length => (rules.get i).normalize.scan)
        (fun i : Fin rules.length => StageFiniteWager.normalizedWager (rules.get i)) V X
        ∂cond (StageFiniteProbability.law cs)
          (block G.get hG.injective_get a ha (wordVector r y)).event := by
  let μ := cond (StageFiniteProbability.law cs)
    (block G.get hG.injective_get a ha (wordVector r y)).event
  have hs : (rules.map fun s => (oneCost s cs G a V y : ℝ)).sum =
      ∑ i : Fin rules.length, (oneCost (rules.get i) cs G a V y : ℝ) := by
    conv_lhs => rw [← List.ofFn_get rules, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [cost, Rat.cast_list_sum, List.map_map]
  change (rules.map fun s => (oneCost s cs G a V y : ℝ)).sum = _
  rw [hs]
  simp only [StageHorizonChoice.objective]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [oneCost, StageConditionalScan.expectation_eq_integral cs G hG a ha]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (statistic_transcript (rules.get i) G hG a ha z V))
  · intro i _
    exact (StageHorizonChoice.integrable_truncated μ _ _ _ V
      (StageFiniteWager.normalizedWager_abs_le_half (rules.get i))).add
      ((integrable_const (1 : ℝ)).indicator (LateDropBound.measurableSet_partialEvent _ _ _))

/-- The chosen syndrome is a total finite computation, and is never advice. -/
noncomputable def chosen (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (G : List ℕ) (a : Entry) (V : ℕ) : List Bool :=
  StageSyndrome.choose (AffineCode.rank a.2) (cost rules cs G a V)

theorem computable_chosen (rules : List BettingStrategy) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ} {a : α → Entry} {V : α → ℕ}
    (hcs : Computable cs) (hG : Computable G) (ha : Computable a) (hV : Computable V) :
    Computable (fun p => chosen rules (cs p) (G p) (a p) (V p)) :=
  StageSyndrome.computable_choose (AffineCode.computable_rank.comp (Computable.snd.comp ha))
    (computable_cost rules (hcs.comp Computable.fst) (hG.comp Computable.fst)
      (ha.comp Computable.fst) (hV.comp Computable.fst) Computable.snd).to₂

theorem chosen_min (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (G : List ℕ) (a : Entry) (V : ℕ) (y : List Bool) (hy : y.length = AffineCode.rank a.2) :
    cost rules cs G a V (chosen rules cs G a V) ≤ cost rules cs G a V y :=
  StageSyndrome.choose_min _ _ y hy

/-- The computed syndrome is an exact minimizer of the actual conditional
integral, with respect to every mathematical syndrome vector. -/
theorem chosen_minimizes_integral (rules : List BettingStrategy)
    (cs : List AffineCode.Data) (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (V : ℕ) :
    ∀ z : Fin r → ZMod 2,
      (∫ X, StageHorizonChoice.objective (block G.get hG.injective_get a ha 0)
        (fun i : Fin rules.length => (rules.get i).normalize.scan)
        (fun i : Fin rules.length => StageFiniteWager.normalizedWager (rules.get i)) V X
        ∂cond (StageFiniteProbability.law cs)
          (block G.get hG.injective_get a ha (wordVector r (chosen rules cs G a V))).event) ≤
      ∫ X, StageHorizonChoice.objective (block G.get hG.injective_get a ha 0)
        (fun i : Fin rules.length => (rules.get i).normalize.scan)
        (fun i : Fin rules.length => StageFiniteWager.normalizedWager (rules.get i)) V X
        ∂cond (StageFiniteProbability.law cs) (block G.get hG.injective_get a ha z).event := by
  intro z
  let yz := List.ofFn (fun i : Fin r => FiniteMeasure.boolEquivF2.symm (z i))
  have hyz : yz.length = AffineCode.rank a.2 := by simp [yz, ha.2.2.2.1]
  have hq := chosen_min rules cs G a V yz hyz
  have hreal : (cost rules cs G a V (chosen rules cs G a V) : ℝ) ≤
      (cost rules cs G a V yz : ℝ) := by exact_mod_cast hq
  rw [cost_eq_integral rules cs G hG a ha V (chosen rules cs G a V) 0,
    cost_eq_integral rules cs G hG a ha V yz 0] at hreal
  simpa only [yz, wordVector_ofFn] using hreal

/-- Finish the stage from a reconstructed horizon, with no syndrome or
certificate supplied as additional input. -/
noncomputable def finish (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (p : (List ℕ × Entry) × ℕ) : Part AffineCode.Data :=
  StageCandidateCode.reconstruct ((p.1.1, p.1.2.2), chosen rules cs p.1.1 p.1.2 p.2)

theorem partrec_finish (rules : List BettingStrategy) (cs : List AffineCode.Data) :
    Partrec (finish rules cs) := by
  have hG : Computable (fun p : (List ℕ × Entry) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have ha : Computable (fun p : (List ℕ × Entry) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  exact StageCandidateCode.partrec_reconstruct.comp
    ((hG.pair (Computable.snd.comp ha)).pair
      (computable_chosen rules (Computable.const cs) hG ha Computable.snd))

theorem finish_halts (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (V : ℕ) :
    ∃ c ∈ finish rules cs ((G, a), V),
      AffineCode.valid c = true ∧ AffineCode.rank c = r ∧
        AffineCode.event c = (block G.get hG.injective_get a ha
          (wordVector r (chosen rules cs G a V))).event :=
  StageCandidateCode.exists_reconstructed_code G hG a ha (chosen rules cs G a V)

end Klr.StageSyndromeObjective

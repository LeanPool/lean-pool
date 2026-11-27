/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageOneStepBounds
public import LeanPool.KLRandomness.StageRankProbability

/-!
# The actual horizon search for one selected candidate

The reconstruction program stores a list of betting strategies. These
lemmas identify its rational rank statistics, computed on the corresponding
list of scans, with the finite-family probabilities in the analytic bounds.
The selected bounded advice therefore makes that very search halt.
-/

@[expose] public section

noncomputable section

namespace Klr.StageOneStep

open MeasureTheory SparseListSearch StageCandidate
open scoped BigOperators

theorem partialSum_map_normalize (rules : List BettingStrategy)
    (cs : List AffineCode.Data) (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2) (V : ℕ) :
    (StageRankProbability.partialSum (rules.map (fun s => s.normalize.scan)) cs G a.2 V : ℝ) =
      StageRankLimit.partialMass (StageFiniteProbability.law cs)
        (block G.get hG.injective_get a ha y)
        (fun i : Fin rules.length => (rules.get i).normalize.scan) V := by
  have hsum : StageRankProbability.partialSum (rules.map (fun s => s.normalize.scan))
      cs G a.2 V = ∑ i : Fin rules.length,
        StageRankProbability.partialProbability cs (rules.get i).normalize.scan G a.2 V := by
    unfold StageRankProbability.partialSum
    rw [List.map_map]
    conv_lhs => rw [← List.ofFn_get rules, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hsum, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact StageRankProbability.partialProbability_eq_measureReal
    cs (rules.get i).normalize.scan G hG a ha y V

theorem dropSum_map_normalize (rules : List BettingStrategy)
    (cs : List AffineCode.Data) (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2) (V : ℕ) :
    (StageRankProbability.dropSum (rules.map (fun s => s.normalize.scan)) cs G a.2 V : ℝ) =
      StageRankLimit.dropMass (StageFiniteProbability.law cs)
        (block G.get hG.injective_get a ha y)
        (fun i : Fin rules.length => (rules.get i).normalize.scan) V := by
  have hsum : StageRankProbability.dropSum (rules.map (fun s => s.normalize.scan))
      cs G a.2 V = ∑ i : Fin rules.length,
        StageRankProbability.dropProbability cs (rules.get i).normalize.scan G a.2 V := by
    unfold StageRankProbability.dropSum
    rw [List.map_map]
    conv_lhs => rw [← List.ofFn_get rules, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hsum, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact StageRankProbability.dropProbability_eq_measureReal
    cs (rules.get i).normalize.scan G hG a ha y V

/-- The bounded-advice search used in the actual reconstruction program
returns a horizon with both required old-law estimates. -/
theorem exists_computed_horizon
    (old : ℕ → AffineBlock)
    (hold : Pairwise (fun i j => Disjoint (old i).support (old j).support))
    (n : ℕ) (rules : List BettingStrategy) (H : Fin rules.length → Set Cantor)
    (cs : List AffineCode.Data)
    (hcs : StageFiniteProbability.law cs = PrefixStage.law old n)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a)
    {error : ℚ} (herror : 0 < error)
    (hhigh : (∑ i : Fin rules.length, (PrefixStage.law old n).real
      (StagePreHorizon.highMissInput (rules.get i) (H i) G)) < (error : ℝ))
    (hlow : (∑ i : Fin rules.length, (PrefixStage.law old n).real
      (StagePreHorizon.lowDropInput (rules.get i) (H i)
        (block G.get hG.injective_get a ha 0))) < (error : ℝ)) :
    ∃ b, b ≤ StageHorizon.adviceBound error rules.length ∧ ∃ V,
      V ∈ StageHorizon.search error
        (StageRankProbability.u (rules.map (fun s => s.normalize.scan)))
        (StageRankProbability.v (rules.map (fun s => s.normalize.scan)))
        (((cs, G), a.2), b) ∧
      StageRankLimit.partialMass (PrefixStage.law old n)
        (block G.get hG.injective_get a ha 0)
        (fun i : Fin rules.length => (rules.get i).normalize.scan) V < 3 * (error : ℝ) ∧
      (∑ i : Fin rules.length, (PrefixStage.law old n).real
        (StoppingTranscript.rankDropTailEvent (block G.get hG.injective_get a ha 0)
          (rules.get i).normalize.scan V)) < 2 * (error : ℝ) := by
  let : IsProbabilityMeasure (PrefixStage.law old n) :=
    PrefixStage.law_isProbabilityMeasure old hold n
  have hu (V : ℕ) :
      (StageRankProbability.u (rules.map (fun s => s.normalize.scan)) ((cs, G), a.2) V : ℝ) =
      StageRankLimit.partialMass (PrefixStage.law old n)
        (block G.get hG.injective_get a ha 0)
        (fun i : Fin rules.length => (rules.get i).normalize.scan) V := by
    simpa only [StageRankProbability.u, hcs] using
      partialSum_map_normalize rules cs G hG a ha 0 V
  have hv (V : ℕ) :
      (StageRankProbability.v (rules.map (fun s => s.normalize.scan)) ((cs, G), a.2) V : ℝ) =
      StageRankLimit.dropMass (PrefixStage.law old n)
        (block G.get hG.injective_get a ha 0)
        (fun i : Fin rules.length => (rules.get i).normalize.scan) V := by
    simpa only [StageRankProbability.v, hcs] using
      dropSum_map_normalize rules cs G hG a ha 0 V
  obtain ⟨b, hb, hdom, hspec⟩ :=
    StageRankLimit.exists_bounded_advice_search_of_rank_probabilities herror
      ((cs, G), a.2) (PrefixStage.law old n) (block G.get hG.injective_get a ha 0)
      (fun i : Fin rules.length => (rules.get i).normalize.scan)
      G.toFinset (block_support_subset G hG a ha 0) H hu hv
      (by simpa only [highMissInput_eq] using hhigh)
      (by simpa only [lowDropInput_eq] using hlow)
  obtain ⟨V, hV⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨haccepted, htail⟩ := hspec V hV
  refine ⟨b, by simpa only [Fintype.card_fin] using hb, V, hV, ?_, htail⟩
  rw [← hu V]
  exact_mod_cast haccepted.1

end Klr.StageOneStep

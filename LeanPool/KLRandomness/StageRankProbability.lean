/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageRankCode
public import LeanPool.KLRandomness.StageFiniteScan
public import LeanPool.KLRandomness.StageRankLimitMeasure

/-!
# Exact rational partial-rank and rank-drop probabilities

The finite rank predicates are evaluated on actual adaptive transcripts,
under the finitely conditioned affine law. Summing over a fixed finite list
of scans gives total computable rational sequences whose real values are
exactly the partial-rank and dropped-by-time masses used by the horizon
convergence theorem.
-/

@[expose] public section

namespace Klr.StageRankProbability

open SparseListSearch StageRankCode RationalComputability
open scoped BigOperators

/-- Exact finite partial-rank probability for one scan. -/
def partialProbability (cs : List AffineCode.Data) (π : ScanRule)
    (G : List ℕ) (c : AffineCode.Data) (V : ℕ) : ℚ :=
  StageFiniteScan.probability cs π V (partialTest π G c)

/-- Exact finite probability that full unread rank has already been lost. -/
def dropProbability (cs : List AffineCode.Data) (π : ScanRule)
    (G : List ℕ) (c : AffineCode.Data) (V : ℕ) : ℚ :=
  StageFiniteScan.probability cs π V (dropTest π G c)

theorem computable_partialProbability (π : ScanRule) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ}
    {c : α → AffineCode.Data} {V : α → ℕ}
    (hcs : Computable cs) (hG : Computable G) (hc : Computable c) (hV : Computable V) :
    Computable (fun p => partialProbability (cs p) π (G p) (c p) (V p)) :=
  StageFiniteScan.computable_probability π hcs hV
    (computable_partialTest π (hG.comp Computable.fst)
      (hc.comp Computable.fst) Computable.snd).to₂

theorem computable_dropProbability (π : ScanRule) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ}
    {c : α → AffineCode.Data} {V : α → ℕ}
    (hcs : Computable cs) (hG : Computable G) (hc : Computable c) (hV : Computable V) :
    Computable (fun p => dropProbability (cs p) π (G p) (c p) (V p)) :=
  StageFiniteScan.computable_probability π hcs hV
    (computable_dropTest π (hG.comp Computable.fst)
      (hc.comp Computable.fst) Computable.snd).to₂

theorem partialProbability_eq_measureReal (cs : List AffineCode.Data) (π : ScanRule)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2) (V : ℕ) :
    (partialProbability cs π G a.2 V : ℝ) =
      (StageFiniteProbability.law cs).real (LateDropBound.partialEvent
        (StageCandidate.block G.get hG.injective_get a ha y) π V) := by
  rw [partialProbability, StageFiniteScan.probability_eq_measureReal]
  apply congrArg (StageFiniteProbability.law cs).real
  ext X
  exact partialTest_eq_true π G hG a ha y (π.transcript X V)

theorem dropProbability_eq_measureReal (cs : List AffineCode.Data) (π : ScanRule)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2) (V : ℕ) :
    (dropProbability cs π G a.2 V : ℝ) =
      (StageFiniteProbability.law cs).real (StageRankLimit.droppedBy
        (StageCandidate.block G.get hG.injective_get a ha y) π V) := by
  rw [dropProbability, StageFiniteScan.probability_eq_measureReal]
  apply congrArg (StageFiniteProbability.law cs).real
  ext X
  exact (dropTest_eq_true π G hG a ha y (π.transcript X V)).trans
    (StageRankLimit.mem_droppedBy_iff _ _ _ _).symm

/-- Sum over a fixed protected list. The scan list is part of the program,
while the old affine codes, pool, candidate code, and horizon vary. -/
def partialSum (rules : List ScanRule) (cs : List AffineCode.Data)
    (G : List ℕ) (c : AffineCode.Data) (V : ℕ) : ℚ :=
  (rules.map fun π => partialProbability cs π G c V).sum

/-- Sum of finite dropped-by-time probabilities over the same protected list. -/
def dropSum (rules : List ScanRule) (cs : List AffineCode.Data)
    (G : List ℕ) (c : AffineCode.Data) (V : ℕ) : ℚ :=
  (rules.map fun π => dropProbability cs π G c V).sum

theorem computable_partialSum (rules : List ScanRule) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ}
    {c : α → AffineCode.Data} {V : α → ℕ}
    (hcs : Computable cs) (hG : Computable G) (hc : Computable c) (hV : Computable V) :
    Computable (fun p => partialSum rules (cs p) (G p) (c p) (V p)) := by
  induction rules with
  | nil => exact Computable.const 0
  | cons π rules ih =>
    exact primrec_rat_add.to_comp.comp (computable_partialProbability π hcs hG hc hV) ih

theorem computable_dropSum (rules : List ScanRule) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ}
    {c : α → AffineCode.Data} {V : α → ℕ}
    (hcs : Computable cs) (hG : Computable G) (hc : Computable c) (hV : Computable V) :
    Computable (fun p => dropSum rules (cs p) (G p) (c p) (V p)) := by
  induction rules with
  | nil => exact Computable.const 0
  | cons π rules ih =>
    exact primrec_rat_add.to_comp.comp (computable_dropProbability π hcs hG hc hV) ih

theorem partialSum_eq_partialMass (rules : List ScanRule) (cs : List AffineCode.Data)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2) (V : ℕ) :
    (partialSum rules cs G a.2 V : ℝ) = StageRankLimit.partialMass
      (StageFiniteProbability.law cs)
      (StageCandidate.block G.get hG.injective_get a ha y) rules.get V := by
  have hsum : partialSum rules cs G a.2 V =
      ∑ i : Fin rules.length, partialProbability cs (rules.get i) G a.2 V := by
    unfold partialSum
    conv_lhs => rw [← List.ofFn_get rules, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hsum, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact partialProbability_eq_measureReal cs (rules.get i) G hG a ha y V

theorem dropSum_eq_dropMass (rules : List ScanRule) (cs : List AffineCode.Data)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2) (V : ℕ) :
    (dropSum rules cs G a.2 V : ℝ) = StageRankLimit.dropMass
      (StageFiniteProbability.law cs)
      (StageCandidate.block G.get hG.injective_get a ha y) rules.get V := by
  have hsum : dropSum rules cs G a.2 V =
      ∑ i : Fin rules.length, dropProbability cs (rules.get i) G a.2 V := by
    unfold dropSum
    conv_lhs => rw [← List.ofFn_get rules, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hsum, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact dropProbability_eq_measureReal cs (rules.get i) G hG a ha y V

/-- Ordinary finite data accepted by the two horizon sequences. -/
abbrev Input := (List AffineCode.Data × List ℕ) × AffineCode.Data

/-- The actual rational sequence `u` for the horizon search. -/
def u (rules : List ScanRule) (input : Input) (n : ℕ) : ℚ :=
  partialSum rules input.1.1 input.1.2 input.2 n

/-- The actual rational sequence `v` for the horizon search. -/
def v (rules : List ScanRule) (input : Input) (n : ℕ) : ℚ :=
  dropSum rules input.1.1 input.1.2 input.2 n

theorem computable_u (rules : List ScanRule) : Computable₂ (u rules) :=
  computable_partialSum rules
    (Computable.fst.comp (Computable.fst.comp Computable.fst))
    (Computable.snd.comp (Computable.fst.comp Computable.fst))
    (Computable.snd.comp Computable.fst) Computable.snd

theorem computable_v (rules : List ScanRule) : Computable₂ (v rules) :=
  computable_dropSum rules
    (Computable.fst.comp (Computable.fst.comp Computable.fst))
    (Computable.snd.comp (Computable.fst.comp Computable.fst))
    (Computable.snd.comp Computable.fst) Computable.snd

/-- The horizon search is partial recursive for the actual finite rank
probabilities, uniformly in the old codes, pool, candidate, and integer advice. -/
theorem partrec_horizonSearch (rules : List ScanRule) (error : ℚ) :
    Partrec (StageHorizon.search error (u rules) (v rules)) :=
  StageHorizon.partrec_search error (computable_u rules) (computable_v rules)

/-- The concrete finite probability sequences make the bounded-advice
horizon search halt for every checked candidate satisfying the two actual
high/low mass bounds. Every returned horizon has the required first-drop
tail estimate. -/
theorem exists_bounded_horizon_search
    (rules : List ScanRule) (cs : List AffineCode.Data)
    (G : List ℕ) (hG : G.Nodup) {m r : ℕ}
    (a : Entry) (ha : GoodEntry G.length m r a) (y : Fin r → ZMod 2)
    (H : Fin rules.length → Set Cantor) {error : ℚ} (herror : 0 < error)
    [MeasureTheory.IsProbabilityMeasure (StageFiniteProbability.law cs)]
    (hhigh : (∑ i : Fin rules.length, (StageFiniteProbability.law cs).real
      ((rules.get i).observationMap ⁻¹' H i ∩
        {X | 0 < PoolQuery.missedCount (rules.get i) G.toFinset
          ((rules.get i).observationMap X)})) < (error : ℝ))
    (hlow : (∑ i : Fin rules.length, (StageFiniteProbability.law cs).real
      ((rules.get i).observationMap ⁻¹' (H i)ᶜ ∩
        LateDropBound.hasDrop (StageCandidate.block G.get hG.injective_get a ha y)
          (rules.get i))) < (error : ℝ)) :
    ∃ advice, advice ≤ StageHorizon.adviceBound error rules.length ∧
      (StageHorizon.search error (u rules) (v rules) (((cs, G), a.2), advice)).Dom ∧
      ∀ horizon,
        horizon ∈ StageHorizon.search error (u rules) (v rules) (((cs, G), a.2), advice) →
        StageHorizon.Accepted error (u rules ((cs, G), a.2))
          (v rules ((cs, G), a.2)) advice horizon ∧
        (∑ i : Fin rules.length, (StageFiniteProbability.law cs).real
          (StoppingTranscript.rankDropTailEvent
            (StageCandidate.block G.get hG.injective_get a ha y) (rules.get i) horizon)) <
          2 * (error : ℝ) := by
  have hsubset : (StageCandidate.block G.get hG.injective_get a ha y).support ⊆
      G.toFinset := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact List.mem_toFinset.mpr (List.get_mem _ _)
  have h := StageRankLimit.exists_bounded_advice_search_of_rank_probabilities
    (u := u rules) (v := v rules) herror ((cs, G), a.2)
    (StageFiniteProbability.law cs)
    (StageCandidate.block G.get hG.injective_get a ha y) rules.get G.toFinset hsubset H
    (fun n => partialSum_eq_partialMass rules cs G hG a ha y n)
    (fun n => dropSum_eq_dropMass rules cs G hG a ha y n) hhigh hlow
  simpa only [Fintype.card_fin] using h

end Klr.StageRankProbability

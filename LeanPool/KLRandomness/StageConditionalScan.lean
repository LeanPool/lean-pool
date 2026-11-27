/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageCandidateCode
public import LeanPool.KLRandomness.StageFiniteCondition
public import LeanPool.KLRandomness.StageFiniteScan

/-!
# Computable expectations after adding a candidate syndrome

The conditioning predicate is evaluated directly on the old affine codes
and the candidate matrix on its concrete pool. Every possible syndrome can
therefore be compared before a certified output code has been reconstructed.
-/

@[expose] public section

namespace Klr.StageConditionalScan

open MeasureTheory ProbabilityTheory SparseSearch SparseListSearch StageCandidate

/-- A prefix length determining the scan and the affine conditions. -/
def depth (cs : List AffineCode.Data) (G : List ℕ) (π : ScanRule) (V : ℕ) : ℕ :=
  StageFiniteScan.depth cs π V + StageCandidateCode.bound G

/-- The finite test for simultaneous satisfaction of old and new affine conditions. -/
def accepts (cs : List AffineCode.Data) (G : List ℕ) (c : AffineCode.Data)
    (y s : List Bool) : Bool :=
  StageFiniteProbability.accepts cs s && StageCandidateCode.table G c y s

/-- The exact rational conditional average of a prefix function. -/
def expectation (cs : List AffineCode.Data) (G : List ℕ) (c : AffineCode.Data)
    (y : List Bool) (π : ScanRule) (V : ℕ) (f : List Bool → ℚ) : ℚ :=
  StageFiniteCondition.expectation (depth cs G π V) (accepts cs G c y)
    (fun s => f (StageFiniteScan.run π s V))

theorem computable_expectation (π : ScanRule) {α : Type*} [Primcodable α]
    {cs : α → List AffineCode.Data} {G : α → List ℕ} {c : α → AffineCode.Data}
    {y : α → List Bool} {V : α → ℕ} {f : α → List Bool → ℚ}
    (hcs : Computable cs) (hG : Computable G) (hc : Computable c)
    (hy : Computable y) (hV : Computable V) (hf : Computable₂ f) :
    Computable (fun a => expectation (cs a) (G a) (c a) (y a) π (V a) (f a)) := by
  have hn := Primrec.nat_add.to_comp.comp
    ((StageFiniteScan.computable_depth π).comp (hcs.pair hV))
    (StageCandidateCode.computable_bound.comp hG)
  have hold := StageFiniteProbability.computable_accepts.comp
    (hcs.comp Computable.fst) Computable.snd
  have hnew := StageCandidateCode.computable_table.comp
    ((((hG.comp Computable.fst).pair (hc.comp Computable.fst)).pair
      (hy.comp Computable.fst)).pair Computable.snd)
  have hp := Primrec.and.to_comp.comp hold hnew
  have hr := (StageFiniteScan.computable_run π).comp Computable.snd (hV.comp Computable.fst)
  exact StageFiniteCondition.computable_expectation hn hp (hf.comp Computable.fst hr)

/-- The finite Boolean condition is exactly old constraints intersected with
the selected affine event. -/
theorem event_eq (cs : List AffineCode.Data) (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : List Bool) (π : ScanRule) (V : ℕ) :
    StageFiniteCondition.event (depth cs G π V) (accepts cs G a.2 y) =
      StageFiniteProbability.event cs ∩
        (block G.get hG.injective_get a ha (wordVector r y)).event := by
  ext X
  change (StageFiniteProbability.accepts cs (ScanRule.inputPrefix X (depth cs G π V)) &&
    StageCandidateCode.table G a.2 y (ScanRule.inputPrefix X (depth cs G π V))) = true ↔ _
  unfold depth
  rw [Bool.and_eq_true,
    StageFiniteProbability.accepts_inputPrefix cs _ (fun c hc =>
      (StageFiniteScan.width_le_depth π V hc).trans (Nat.le_add_right _ _)),
    StageCandidateCode.table_inputPrefix G hG a ha y _ (Nat.le_add_left _ _) X]
  rfl

/-- Exact rational evaluation under the actual old law conditioned on the
new candidate syndrome. No affine output code is assumed in this identity. -/
theorem expectation_eq_integral (cs : List AffineCode.Data) (G : List ℕ) (hG : G.Nodup)
    {m r : ℕ} (a : Entry) (ha : GoodEntry G.length m r a)
    (y : List Bool) (π : ScanRule) (V : ℕ) (f : List Bool → ℚ) :
    (expectation cs G a.2 y π V f : ℝ) =
      ∫ X, (f (π.transcript X V) : ℝ) ∂cond (StageFiniteProbability.law cs)
        (block G.get hG.injective_get a ha (wordVector r y)).event := by
  rw [expectation, StageFiniteCondition.expectation_eq_integral, event_eq cs G hG a ha]
  rw [StageFiniteProbability.law, cond_cond_eq_cond_inter
    (StageFiniteProbability.measurableSet_event cs)
    (block G.get hG.injective_get a ha (wordVector r y)).measurableSet_event fairCoin]
  apply integral_congr_ae
  filter_upwards [] with X
  unfold depth
  rw [StageFiniteScan.run_inputPrefix_of_bound π V _ (fun v hv =>
    (StageFiniteScan.query_lt_depth cs π V v hv).trans_le (Nat.le_add_right _ _)) X le_rfl]

end Klr.StageConditionalScan

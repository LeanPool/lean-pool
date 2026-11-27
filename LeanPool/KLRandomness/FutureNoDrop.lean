/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.BlockProduct
import Mathlib.Tactic.Push

/-!
# No-drop restrictions for the infinite block law

The infinite block law and stage `j` agree on every Borel transcript event
restricted to paths on which no block `k ≥ j` ever loses full unread rank.
The proof derives equality on finite surviving transcript partitions, passes
to a decreasing intersection, and uses uniqueness on the cylinder generator.
The restrictions are not normalized, so zero-mass no-drop events are included.
-/

@[expose] public section

namespace Klr.FutureNoDrop

open MeasureTheory ProbabilityTheory StoppingTranscript
open scoped ENNReal

/-- Every block not yet imposed at stage `j` retains full unread rank. -/
def Safe (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) (v : List Bool) : Prop :=
  ∀ k, j ≤ k → (B k).UnreadFullRank π v

/-- No future block has lost full rank after `n` observed answers. -/
def survivalEvent (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) (n : ℕ) : Set Cantor :=
  {X | Safe B j π (π.transcript X n)}

/-- No future block ever loses full unread rank, as an event of inputs. -/
def noDropEvent (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) : Set Cantor :=
  {X | ∀ n, Safe B j π (π.transcript X n)}

/-- No future block ever loses full unread rank, as an event of infinite transcripts. -/
def noDropTranscripts (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) : Set Cantor :=
  {Y | ∀ n, Safe B j π (ScanRule.inputPrefix Y n)}

theorem survivalEvent_antitone (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) :
    Antitone (survivalEvent B j π) := by
  intro m n h X hX k hk
  exact NoDrop.survivalEvent_antitone (B k) π h (hX k hk)

theorem noDropEvent_eq_iInter (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) :
    noDropEvent B j π = ⋂ n, survivalEvent B j π n := by
  ext X
  simp [noDropEvent, survivalEvent]

theorem noDropEvent_eq_iInter_blocks (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) :
    noDropEvent B j π = ⋂ k : {k : ℕ // j ≤ k}, NoDrop.noDropEvent (B k.val) π := by
  ext X
  simp only [noDropEvent, Safe, NoDrop.noDropEvent, Set.mem_ofPred_eq, Set.mem_iInter]
  exact ⟨fun h k n => h n k.val k.property, fun h n k hk => h ⟨k, hk⟩ n⟩

theorem measurableSet_noDropEvent (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) :
    MeasurableSet (noDropEvent B j π) := by
  rw [noDropEvent_eq_iInter_blocks]
  exact MeasurableSet.iInter (fun k => NoDrop.measurableSet_noDropEvent (B k.val) π)

theorem measurableSet_noDropTranscripts (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) :
    MeasurableSet (noDropTranscripts B j π) := by
  change MeasurableSet {Y | ∀ n, Safe B j π (ScanRule.inputPrefix Y n)}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_prefix_event (Safe B j π) n)

theorem observationMap_preimage_noDropTranscripts (B : ℕ → AffineBlock) (j : ℕ)
    (π : ScanRule) :
    π.observationMap ⁻¹' noDropTranscripts B j π = noDropEvent B j π := by
  ext X
  simp only [Set.mem_preimage, noDropTranscripts, noDropEvent, Set.mem_ofPred_eq,
    π.inputPrefix_observationMap]

/-- The event is exactly absence of every finite strict rank drop in any future block. -/
theorem mem_noDropEvent_iff_no_strict_rank_drop (B : ℕ → AffineBlock) (j : ℕ)
    (π : ScanRule) (X : Cantor) :
    X ∈ noDropEvent B j π ↔ ∀ k, j ≤ k → ∀ n,
      ¬(B k).remainingRank π (π.transcript X (n + 1)) <
        (B k).remainingRank π (π.transcript X n) := by
  rw [noDropEvent_eq_iInter_blocks]
  simp only [Set.mem_iInter, NoDrop.mem_noDropEvent_iff_no_strict_rank_drop]
  exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k.val k.property⟩

/-- Length-`n` extensions whose unread columns remain full rank on every future block. -/
def survivingExtensions (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule)
    (v : List Bool) (n : ℕ) : Set (List Bool) :=
  {w | w.length = n ∧ v <+: w ∧ Safe B j π w}

theorem survivingExtensions_prefixFree (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule)
    (v : List Bool) (n : ℕ) : PrefixFree (survivingExtensions B j π v n) := by
  intro u w hu hw h
  exact h.eq_of_length (hu.1.trans hw.1.symm)

theorem inputEvent_inter_survival_eq_union (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule)
    (v : List Bool) (n : ℕ) (hn : v.length ≤ n) :
    inputEvent π v ∩ survivalEvent B j π n =
      unionEvent π (survivingExtensions B j π v n) := by
  ext X
  constructor
  · rintro ⟨hv, hfull⟩
    change π.transcript X v.length = v at hv
    have hw : π.transcript X n ∈ survivingExtensions B j π v n := by
      refine ⟨π.length_transcript X n, ?_, hfull⟩
      simpa only [hv] using π.transcript_prefix X hn
    apply Set.mem_iUnion.mpr
    refine ⟨⟨π.transcript X n, hw⟩, ?_⟩
    change π.transcript X (π.transcript X n).length = π.transcript X n
    rw [π.length_transcript]
  · intro h
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
    refine ⟨inputEvent_subset_of_prefix π w.property.2.1 hw, ?_⟩
    change π.transcript X w.val.length = w.val at hw
    rw [w.property.1] at hw
    change Safe B j π (π.transcript X n)
    rw [hw]
    exact w.property.2.2

theorem measurableSet_survivalEvent (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule)
    (n : ℕ) : MeasurableSet (survivalEvent B j π n) := by
  have h := inputEvent_inter_survival_eq_union B j π [] n (by simp)
  have he : inputEvent π [] = Set.univ := by
    ext X
    simp [inputEvent]
  rw [he, Set.univ_inter] at h
  rw [h]
  exact measurableSet_unionEvent π _

theorem law_inputEvent_inter_survival (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) (v : List Bool) (n : ℕ) (hn : v.length ≤ n) :
    BlockProduct.law B hdis (inputEvent π v ∩ survivalEvent B j π n) =
      PrefixStage.law B j (inputEvent π v ∩ survivalEvent B j π n) := by
  rw [inputEvent_inter_survival_eq_union B j π v n hn]
  exact BlockProduct.law_unionEvent_eq_of_fullRank B hdis j π
    (survivingExtensions_prefixFree B j π v n) (fun _ hw => hw.2.2)

theorem inputEvent_inter_noDrop_eq_iInter (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule)
    (v : List Bool) :
    inputEvent π v ∩ noDropEvent B j π =
      ⋂ n, inputEvent π v ∩ survivalEvent B j π (n + v.length) := by
  ext X
  constructor
  · rintro ⟨hv, hfull⟩
    exact Set.mem_iInter.mpr (fun n => ⟨hv, hfull _⟩)
  · intro h
    have h' := Set.mem_iInter.mp h
    refine ⟨(h' 0).1, ?_⟩
    intro n
    exact survivalEvent_antitone B j π (Nat.le_add_right n v.length) (h' n).2

/-- Equality survives the decreasing limit to paths with no future rank drop. -/
theorem law_inputEvent_inter_noDrop (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) (v : List Bool) :
    BlockProduct.law B hdis (inputEvent π v ∩ noDropEvent B j π) =
      PrefixStage.law B j (inputEvent π v ∩ noDropEvent B j π) := by
  have ha : Antitone (fun n => inputEvent π v ∩ survivalEvent B j π (n + v.length)) := by
    intro m n h X hX
    exact ⟨hX.1, survivalEvent_antitone B j π (Nat.add_le_add_right h _) hX.2⟩
  have hm (n : ℕ) : MeasurableSet (inputEvent π v ∩ survivalEvent B j π (n + v.length)) :=
    (measurableSet_inputEvent π v).inter (measurableSet_survivalEvent B j π _)
  let : IsProbabilityMeasure (PrefixStage.law B j) := PrefixStage.law_isProbabilityMeasure B hdis j
  rw [inputEvent_inter_noDrop_eq_iInter,
    ha.measure_iInter (fun n => (hm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
    ha.measure_iInter (fun n => (hm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact iInf_congr fun n => law_inputEvent_inter_survival B hdis j π v
    (n + v.length) (Nat.le_add_left _ _)

/-- The actual infinite and stage-`j` transcript laws have identical no-future-drop restrictions. -/
theorem law_map_restrict_noDrop (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) :
    ((BlockProduct.law B hdis).map π.observationMap).restrict (noDropTranscripts B j π) =
      ((PrefixStage.law B j).map π.observationMap).restrict (noDropTranscripts B j π) := by
  apply measure_eq_of_cylinders
  intro v
  have hm := (measurableSet_cylinder v).inter (measurableSet_noDropTranscripts B j π)
  rw [Measure.restrict_apply (measurableSet_cylinder v),
    Measure.restrict_apply (measurableSet_cylinder v),
    Measure.map_apply π.measurable_observationMap hm,
    Measure.map_apply π.measurable_observationMap hm,
    Set.preimage_inter, π.observationMap_preimage_cylinder,
    observationMap_preimage_noDropTranscripts]
  exact law_inputEvent_inter_noDrop B hdis j π v

/-- Equality for every Borel transcript event on paths without a rank drop in any block `k ≥ j`. -/
theorem law_noDrop_borel (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) {F : Set Cantor} (hF : MeasurableSet F) :
    BlockProduct.law B hdis (π.observationMap ⁻¹' F ∩ noDropEvent B j π) =
      PrefixStage.law B j (π.observationMap ⁻¹' F ∩ noDropEvent B j π) := by
  have h := congrArg (fun μ : Measure Cantor => μ F) (law_map_restrict_noDrop B hdis j π)
  rw [Measure.restrict_apply hF, Measure.restrict_apply hF,
    Measure.map_apply π.measurable_observationMap
      (hF.inter (measurableSet_noDropTranscripts B j π)),
    Measure.map_apply π.measurable_observationMap
      (hF.inter (measurableSet_noDropTranscripts B j π)),
    Set.preimage_inter, observationMap_preimage_noDropTranscripts] at h
  exact h

theorem law_survivalEvent (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) (N : ℕ) :
    BlockProduct.law B hdis (survivalEvent B j π N) =
      PrefixStage.law B j (survivalEvent B j π N) := by
  simpa [inputEvent] using law_inputEvent_inter_survival B hdis j π [] N (by simp)

theorem law_noDropEvent (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) :
    BlockProduct.law B hdis (noDropEvent B j π) =
      PrefixStage.law B j (noDropEvent B j π) := by
  simpa using law_noDrop_borel B hdis j π MeasurableSet.univ

theorem noDropEvent_subset_survivalEvent (B : ℕ → AffineBlock) (j : ℕ)
    (π : ScanRule) (N : ℕ) : noDropEvent B j π ⊆ survivalEvent B j π N :=
  fun _ h => h N

/-- The first rank drop on any future block occurs after horizon `N`, at a finite query. -/
def firstDropAfter (B : ℕ → AffineBlock) (j : ℕ) (π : ScanRule) (N : ℕ) : Set Cantor :=
  survivalEvent B j π N \ noDropEvent B j π

theorem measurableSet_firstDropAfter (B : ℕ → AffineBlock) (j : ℕ)
    (π : ScanRule) (N : ℕ) : MeasurableSet (firstDropAfter B j π N) :=
  (measurableSet_survivalEvent B j π N).diff (measurableSet_noDropEvent B j π)

/-- The stopping tail has the paper's one-based query interpretation.  Every future
block is still full rank at `N`, and some future block has a strict decrease at a later query. -/
theorem mem_firstDropAfter_iff (B : ℕ → AffineBlock) (j : ℕ)
    (π : ScanRule) (N : ℕ) (X : Cantor) :
    X ∈ firstDropAfter B j π N ↔
      Safe B j π (π.transcript X N) ∧ ∃ k, j ≤ k ∧ ∃ t, N < t ∧
        (B k).remainingRank π (π.transcript X t) <
          (B k).remainingRank π (π.transcript X (t - 1)) := by
  classical
  constructor
  · rintro ⟨hN, hno⟩
    rw [mem_noDropEvent_iff_no_strict_rank_drop] at hno
    push Not at hno
    obtain ⟨k, hk, n, hdrop⟩ := hno
    refine ⟨hN, k, hk, n + 1, ?_, by simpa using hdrop⟩
    by_contra h
    have hnN : n + 1 ≤ N := by omega
    have hn1 := survivalEvent_antitone B j π hnN hN k hk
    have hn0 := survivalEvent_antitone B j π (show n ≤ N by omega) hN k hk
    rw [(B k).unreadFullRank_iff_remainingRank] at hn1 hn0
    rw [hn1, hn0] at hdrop
    exact lt_irrefl _ hdrop
  · rintro ⟨hN, k, hk, t, ht, hdrop⟩
    refine ⟨hN, ?_⟩
    intro hno
    have h := (mem_noDropEvent_iff_no_strict_rank_drop B j π X).mp hno k hk (t - 1)
    have ht1 : 1 ≤ t := by omega
    rw [Nat.sub_add_cancel ht1] at h
    exact h hdrop

/-- The infinite and finite-stage laws agree on the first-future-drop tail. -/
theorem law_firstDropAfter (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j : ℕ) (π : ScanRule) (N : ℕ) :
    BlockProduct.law B hdis (firstDropAfter B j π N) =
      PrefixStage.law B j (firstDropAfter B j π N) := by
  let : IsProbabilityMeasure (PrefixStage.law B j) := PrefixStage.law_isProbabilityMeasure B hdis j
  rw [firstDropAfter,
    measure_sdiff (noDropEvent_subset_survivalEvent B j π N)
      (measurableSet_noDropEvent B j π).nullMeasurableSet (measure_ne_top _ _),
    measure_sdiff (noDropEvent_subset_survivalEvent B j π N)
      (measurableSet_noDropEvent B j π).nullMeasurableSet (measure_ne_top _ _),
    law_survivalEvent B hdis j π N, law_noDropEvent B hdis j π]

/-- The safety cutoff may precede the comparison stage: retaining full rank on all
blocks `k ≥ j` in particular retains it on every not-yet-imposed block `k ≥ n`. -/
theorem law_inputEvent_inter_survival_of_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j n : ℕ) (hjn : j ≤ n) (π : ScanRule) (v : List Bool) (N : ℕ)
    (hN : v.length ≤ N) :
    BlockProduct.law B hdis (inputEvent π v ∩ survivalEvent B j π N) =
      PrefixStage.law B n (inputEvent π v ∩ survivalEvent B j π N) := by
  rw [inputEvent_inter_survival_eq_union B j π v N hN]
  apply BlockProduct.law_unionEvent_eq_of_fullRank B hdis n π
    (survivingExtensions_prefixFree B j π v N)
  intro w hw k hk
  exact hw.2.2 k (hjn.trans hk)

theorem law_inputEvent_inter_noDrop_of_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j n : ℕ) (hjn : j ≤ n) (π : ScanRule) (v : List Bool) :
    BlockProduct.law B hdis (inputEvent π v ∩ noDropEvent B j π) =
      PrefixStage.law B n (inputEvent π v ∩ noDropEvent B j π) := by
  have ha : Antitone (fun N => inputEvent π v ∩ survivalEvent B j π (N + v.length)) := by
    intro a b h X hX
    exact ⟨hX.1, survivalEvent_antitone B j π (Nat.add_le_add_right h _) hX.2⟩
  have hm (N : ℕ) : MeasurableSet (inputEvent π v ∩ survivalEvent B j π (N + v.length)) :=
    (measurableSet_inputEvent π v).inter (measurableSet_survivalEvent B j π _)
  let : IsProbabilityMeasure (PrefixStage.law B n) := PrefixStage.law_isProbabilityMeasure B hdis n
  rw [inputEvent_inter_noDrop_eq_iInter,
    ha.measure_iInter (fun N => (hm N).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
    ha.measure_iInter (fun N => (hm N).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  exact iInf_congr fun N => law_inputEvent_inter_survival_of_le B hdis j n hjn π v
    (N + v.length) (Nat.le_add_left _ _)

/-- General no-drop restriction equality with a safety cutoff `j` and any stage `n ≥ j`. -/
theorem law_map_restrict_noDrop_of_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j n : ℕ) (hjn : j ≤ n) (π : ScanRule) :
    ((BlockProduct.law B hdis).map π.observationMap).restrict (noDropTranscripts B j π) =
      ((PrefixStage.law B n).map π.observationMap).restrict (noDropTranscripts B j π) := by
  apply measure_eq_of_cylinders
  intro v
  have hm := (measurableSet_cylinder v).inter (measurableSet_noDropTranscripts B j π)
  rw [Measure.restrict_apply (measurableSet_cylinder v),
    Measure.restrict_apply (measurableSet_cylinder v),
    Measure.map_apply π.measurable_observationMap hm,
    Measure.map_apply π.measurable_observationMap hm,
    Set.preimage_inter, π.observationMap_preimage_cylinder,
    observationMap_preimage_noDropTranscripts]
  exact law_inputEvent_inter_noDrop_of_le B hdis j n hjn π v

theorem law_noDrop_borel_of_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j n : ℕ) (hjn : j ≤ n) (π : ScanRule) {F : Set Cantor} (hF : MeasurableSet F) :
    BlockProduct.law B hdis (π.observationMap ⁻¹' F ∩ noDropEvent B j π) =
      PrefixStage.law B n (π.observationMap ⁻¹' F ∩ noDropEvent B j π) := by
  have h := congrArg (fun μ : Measure Cantor => μ F)
    (law_map_restrict_noDrop_of_le B hdis j n hjn π)
  rw [Measure.restrict_apply hF, Measure.restrict_apply hF,
    Measure.map_apply π.measurable_observationMap
      (hF.inter (measurableSet_noDropTranscripts B j π)),
    Measure.map_apply π.measurable_observationMap
      (hF.inter (measurableSet_noDropTranscripts B j π)),
    Set.preimage_inter, observationMap_preimage_noDropTranscripts] at h
  exact h

/-- The first-future-drop tail can be compared with a stage that already contains
the first of the tracked blocks. The case `n = j + 1` is the Section 6 comparison. -/
theorem law_firstDropAfter_of_le (B : ℕ → AffineBlock)
    (hdis : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (j n : ℕ) (hjn : j ≤ n) (π : ScanRule) (N : ℕ) :
    BlockProduct.law B hdis (firstDropAfter B j π N) =
      PrefixStage.law B n (firstDropAfter B j π N) := by
  have hs : BlockProduct.law B hdis (survivalEvent B j π N) =
      PrefixStage.law B n (survivalEvent B j π N) := by
    simpa [inputEvent] using
      law_inputEvent_inter_survival_of_le B hdis j n hjn π [] N (by simp)
  have hd : BlockProduct.law B hdis (noDropEvent B j π) =
      PrefixStage.law B n (noDropEvent B j π) := by
    simpa using law_noDrop_borel_of_le B hdis j n hjn π MeasurableSet.univ
  let : IsProbabilityMeasure (PrefixStage.law B n) := PrefixStage.law_isProbabilityMeasure B hdis n
  rw [firstDropAfter,
    measure_sdiff (noDropEvent_subset_survivalEvent B j π N)
      (measurableSet_noDropEvent B j π).nullMeasurableSet (measure_ne_top _ _),
    measure_sdiff (noDropEvent_subset_survivalEvent B j π N)
      (measurableSet_noDropEvent B j π).nullMeasurableSet (measure_ne_top _ _), hs, hd]

end Klr.FutureNoDrop

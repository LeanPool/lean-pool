/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DefectiveVertex
public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.ExtensionBaseActiveIndices
public import LeanPool.GoldbergSeymour.ExtensionBaseDeltaExclusion
public import LeanPool.GoldbergSeymour.ExtensionBaseSameSupportStoredPairOverlap
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClassEnumeration
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClassColors
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportOrder
public import LeanPool.GoldbergSeymour.ExtensionRules
public import LeanPool.GoldbergSeymour.MaximumDefectiveChoice
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

public import LeanPool.GoldbergSeymour.LowerRoundProperties

/-!
# Extension Base Stored Pair Overlap

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ExtensionBaseStoredPairOverlap_sameSupport_239.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
    TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
    e0 input T generating) (terminalSupport : V) (hterminalSupport : terminalSupport ∈
    TreeSequenceVertexSet T) (q : Fin ett.rounds), (↑q : ℕ) + 1 = ett.rounds → ((∀ (s t : Fin
    ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈ TreeSequenceVertexSet T → s ∈
    ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → t ∈
    ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → (↑s : ℕ) < (↑t : ℕ) →
    ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
    vt → vt = vs ∨ TreeVertexOrder T vt vs) ∧ (∀ (s : Fin ett.rounds) (vs : V) (hvsFinal : vs
    ∈ TreeSequenceVertexSet T), s ∈ ExtensionBaseActiveIndices ett terminalSupport
    hterminalSupport → ett.series.data.chosenVertex s.succ = some vs → ETTFirstAppearanceIndex
    ett vs hvsFinal = ETTFirstAppearanceIndex ett terminalSupport hterminalSupport ∧
    (terminalSupport = vs ∨ TreeVertexOrder T terminalSupport vs)) ∧ ∀ (s t : Fin ett.rounds)
    (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈ TreeSequenceVertexSet T → s ∈
    ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → t ∈
    ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
    ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
    vt → vs ≠ vt → TreeVertexOrder T vs vt → (↑t : ℕ) < (↑s : ℕ)) → (∀ (s t : Fin ett.rounds)
    (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈ TreeSequenceVertexSet T → ∀ (deltaT
    gammaS : Fin k), s ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → t ∈
    ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → (↑s : ℕ) ≤ (↑t : ℕ) →
    ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
    vt → ett.series.data.delta t.succ = some deltaT → ett.series.data.gamma s.succ = some
    gammaS → deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
    (ett.series.data.tree s.succ.castSucc) ∧ deltaT ≠ gammaS) → ∀ (s t : Fin ett.rounds) (vs
    vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈ TreeSequenceVertexSet T → ∀ (gammaS deltaS
    gammaT deltaT : Fin k), s ∈ ExtensionBaseActiveIndices ett terminalSupport
    hterminalSupport → t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
    (↑s : ℕ) < (↑t : ℕ) → ett.series.data.chosenVertex s.succ = some vs →
    ett.series.data.chosenVertex t.succ = some vt → ett.series.data.gamma s.succ = some gammaS
    → ett.series.data.delta s.succ = some deltaS → ett.series.data.gamma t.succ = some gammaT
    → ett.series.data.delta t.succ = some deltaT → vs = vt → ((ett.series.data.stored s.succ ∩
    ett.series.data.stored t.succ).Nonempty ↔ ¬∃ r ∈ ExtensionBaseActiveIndices ett
    terminalSupport hterminalSupport, (↑s : ℕ) < (↑r : ℕ) ∧ (↑r : ℕ) < (↑t : ℕ) ∧
    ett.series.data.chosenVertex r.succ = some vs) ∧ ((ett.series.data.stored s.succ ∩
    ett.series.data.stored t.succ).Nonempty → ett.series.data.stored s.succ ∩
    ett.series.data.stored t.succ = {gammaT} ∧ ett.series.data.stored s.succ ∩
    ett.series.data.stored t.succ = {deltaS}) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport q hqTerminal
      supportOrder deltaExclusion s t vs vt hvsFinal hvtFinal gammaS deltaS gammaT deltaT
      hsActive htActive hst hsVertex htVertex hsGamma hsDelta htGamma htDelta hvst
  subst vt
  have hsClass : s ∈ ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport vs := by
    simp [ExtensionBaseSupportClass, hsActive, hsVertex]
  have htClass : t ∈ ExtensionBaseSupportClass ett terminalSupport
      hterminalSupport vs := by
    simp [ExtensionBaseSupportClass, htActive, htVertex]
  have hclassNonempty :
      (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport vs).Nonempty := ⟨s, hsClass⟩
  have hcommon :
    ∀ (r : Fin ett.rounds) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T), r ∈
        ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        ett.series.data.chosenVertex r.succ = some v → ETTFirstAppearanceIndex ett v hvFinal =
        ETTFirstAppearanceIndex ett terminalSupport hterminalSupport := by
    intro r v hvFinal hrActive hrVertex
    exact (supportOrder.2.1 r v hvFinal hrActive hrVertex).1
  obtain ⟨p, indices, hwCurrent, hincreasing, hclass, henumerates⟩ :=
    ExtensionBaseSupportClassEnumeration ett terminalSupport
      hterminalSupport q hqTerminal vs hcommon hclassNonempty
  have hdeltaIndexed :
    ∀ (a b : Fin (p + 1)) (gammaA deltaB : Fin k), a.val ≤ b.val → ett.series.data.gamma (indices
        a).succ = some gammaA → ett.series.data.delta (indices b).succ = some deltaB → deltaB ≠
        gammaA := by
    intro a b gammaA deltaB hab haGamma hbDelta
    have haClass := (hclass (indices a)).2 ⟨a, rfl⟩
    have hbClass := (hclass (indices b)).2 ⟨b, rfl⟩
    simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haClass hbClass
    have habIndices : (indices a).val ≤ (indices b).val := by
      rcases lt_or_eq_of_le hab with hablt | habeq
      · exact (hincreasing a b hablt).le
      · have habFin : a = b := Fin.ext habeq
        subst b
        exact le_rfl
    exact (deltaExclusion (indices a) (indices b) vs vs hvsFinal
      hvsFinal deltaB gammaA haClass.1 hbClass.1 habIndices
      haClass.2 hbClass.2 hbDelta haGamma).2
  have hsame := ExtensionBaseSameSupportStoredPairOverlap ett
    terminalSupport hterminalSupport q hqTerminal vs hwCurrent p indices
    hincreasing hclass henumerates hdeltaIndexed s t hsClass htClass hst
    gammaS deltaS gammaT deltaT hsGamma hsDelta htGamma htDelta
  have hbetween :
      (∃ r : Fin ett.rounds,
        r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport vs ∧
        s.val < r.val ∧ r.val < t.val) ↔
      ∃ r : Fin ett.rounds,
        r ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport ∧
        s.val < r.val ∧ r.val < t.val ∧
        ett.series.data.chosenVertex r.succ = some vs := by
    constructor
    · rintro ⟨r, hrClass, hsr, hrt⟩
      simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hrClass
      exact ⟨r, hrClass.1, hsr, hrt, hrClass.2⟩
    · rintro ⟨r, hrActive, hsr, hrt, hrVertex⟩
      refine ⟨r, ?_, hsr, hrt⟩
      simp [ExtensionBaseSupportClass, hrActive, hrVertex]
  constructor
  · constructor
    · intro hoverlap hbetweenActive
      exact (hsame.1.mp hoverlap) (hbetween.mpr hbetweenActive)
    · intro hnoClass
      apply hsame.1.mpr
      intro hbetweenClass
      exact hnoClass (hbetween.mp hbetweenClass)
  · exact hsame.2

theorem ExtensionBaseStoredPairOverlap {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (jSlot : Fin ett.rounds)
    (hjSlot : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hMP : MaximumProperty ett)
    (hpositive : 0 < ett.rounds)
    (hLowerElementary : ∀ r : Fin ett.rounds, r.val < q.val →
      ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree r.succ.castSucc)))
    (hLowerPartV : ∀ (r a : Fin ett.rounds), a.val < r.val →
      ∀ sigma : PartialEdgeColoring E k,
        IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring (ett.series.data.tree r.succ.castSucc)
          (TashkinovStoredColors ett.series.data r.castSucc)
          (ett.series.data.coloring r.castSucc) sigma →
        ∀ delta : Fin k,
          DefectiveColor G sigma
            (TreeSequenceVertexSet
              (ett.series.data.tree r.succ.castSucc)) delta →
          ∀ v : V,
            BoundaryColorVertex G sigma
              (TreeSequenceVertexSet
                (ett.series.data.tree r.succ.castSucc)) delta v →
            (∃ w : V, BoundaryColorVertex G sigma
                (TreeSequenceVertexSet
                  (ett.series.data.tree r.succ.castSucc)) delta w ∧
              TreeVertexOrder (ett.series.data.tree r.succ.castSucc) w v) →
            ∀ hvFinal : v ∈ TreeSequenceVertexSet T,
              ETTFirstAppearanceIndex ett v hvFinal ≤ a.val + 1 →
              ∀ va : V,
                (ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.PE ∨
                  ett.series.data.kind a.succ =
                    some TashkinovExtensionKind.SE) →
                ett.series.data.chosenVertex a.succ = some va →
                v = va ∨
                  TreeVertexOrder
                    (ett.series.data.tree r.succ.castSucc) v va)
    (hlower : ∀ {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (lower : ExtendedTashkinovTree G k e0 input T' generating'),
      0 < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
      (open scoped Classical in LowerRoundProperties lower)) :
    ∀ (s t : Fin ett.rounds) (vs vt : V) (_ : vs ∈ TreeSequenceVertexSet T) (_ : vt ∈
        TreeSequenceVertexSet T) (gammaS deltaS gammaT deltaT : Fin k), s ∈
        ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → t ∈
        ExtensionBaseActiveIndices ett terminalSupport hterminalSupport → s.val < t.val →
        ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
        vt → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ = some
        deltaS → ett.series.data.gamma t.succ = some gammaT → ett.series.data.delta t.succ = some
        deltaT → ((ett.series.data.stored s.succ ∩ ett.series.data.stored t.succ).Nonempty ↔ vs =
        vt ∧ ¬
    ∃ r : Fin ett.rounds, r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport ∧
        s.val < r.val ∧ r.val < t.val ∧ ett.series.data.chosenVertex r.succ = some vs) ∧
        ((ett.series.data.stored s.succ ∩ ett.series.data.stored t.succ).Nonempty →
        ett.series.data.stored s.succ ∩ ett.series.data.stored t.succ = {gammaT} ∧
        ett.series.data.stored s.succ ∩ ett.series.data.stored t.succ = {deltaS}) := by
  classical
  have supportOrder := ExtensionBaseSupportOrder ett terminalSupport
    hterminalSupport q hqTerminal hqKind hqVertex hLowerPartV
  have deltaExclusion := (ExtensionBaseDeltaExclusion ett terminalSupport
    hterminalSupport q hqTerminal hqKind hqVertex jSlot hjSlot
    hLowerElementary hLowerPartV).1
  have differentSupport := (ExtensionRules G k e0 input T generating ett
    hMP hpositive hlower).2
  intro s t vs vt hvsFinal hvtFinal gammaS deltaS gammaT deltaT
    hsActive htActive hst hsVertex htVertex hsGamma hsDelta htGamma htDelta
  have hsKind : ett.series.data.kind s.succ =
      some TashkinovExtensionKind.PE := by
    have hsData := hsActive
    simp only [ExtensionBaseActiveIndices, exists_and_left, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsData
    exact hsData.2.1
  have htKind : ett.series.data.kind t.succ =
      some TashkinovExtensionKind.PE := by
    have htData := htActive
    simp only [ExtensionBaseActiveIndices, exists_and_left, Finset.mem_filter, Finset.mem_univ,
    true_and] at htData
    exact htData.2.1
  have sameSupport : vs = vt →
      (((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty ↔
        ¬ ∃ r : Fin ett.rounds,
          r ∈ ExtensionBaseActiveIndices ett terminalSupport
            hterminalSupport ∧
          s.val < r.val ∧ r.val < t.val ∧
          ett.series.data.chosenVertex r.succ = some vs) ∧
      ((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty →
        ett.series.data.stored s.succ ∩
            ett.series.data.stored t.succ = {gammaT} ∧
          ett.series.data.stored s.succ ∩
            ett.series.data.stored t.succ = {deltaS})) := by
    exact @ExtensionBaseStoredPairOverlap_sameSupport_239 V E inferInstance inferInstance
         inferInstance G k e0 input T generating ett terminalSupport
        hterminalSupport q hqTerminal supportOrder deltaExclusion s t vs vt hvsFinal hvtFinal
        gammaS deltaS gammaT deltaT hsActive htActive hst hsVertex htVertex hsGamma hsDelta
        htGamma htDelta
  have hoverlapIff :
      ((ett.series.data.stored s.succ ∩
          ett.series.data.stored t.succ).Nonempty ↔
        vs = vt ∧
          ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseActiveIndices ett terminalSupport
              hterminalSupport ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) := by
    constructor
    · intro hoverlap
      by_cases hvst : vs = vt
      · exact ⟨hvst, (sameSupport hvst).1.mp hoverlap⟩
      · have hstNe : s ≠ t := by
          intro heq
          subst t
          omega
        have hsFirst :=
          (supportOrder.2.1 s vs hvsFinal hsActive hsVertex).1
        have htFirst :=
          (supportOrder.2.1 t vt hvtFinal htActive htVertex).1
        have hdisjoint := differentSupport s t vs vt hstNe hvst hsKind
          htKind hsVertex htVertex hvsFinal hvtFinal
          (hsFirst.trans htFirst.symm)
        obtain ⟨c, hc⟩ := hoverlap
        have hcPairs := Finset.mem_inter.mp hc
        exact (Finset.disjoint_left.mp hdisjoint hcPairs.1 hcPairs.2).elim
    · rintro ⟨hvst, hnoBetween⟩
      exact (sameSupport hvst).1.mpr hnoBetween
  refine ⟨hoverlapIff, ?_⟩
  intro hoverlap
  have hvst := (hoverlapIff.mp hoverlap).1
  exact (sameSupport hvst).2 hoverlap

end GoldbergSeymour

end

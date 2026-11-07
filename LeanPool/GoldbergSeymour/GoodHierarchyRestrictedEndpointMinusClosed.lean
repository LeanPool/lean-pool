/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.BoundaryMissingColorAugmentation
public import LeanPool.GoldbergSeymour.GoodHierarchy

public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff

public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors

/-!
# Good Hierarchy Restricted Endpoint Minus Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchyRestrictedEndpointMinusClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    {inputJ inputU : PartialEdgeColoring E k}
    (J U : TreeSequence G e0) (sigma : PartialEdgeColoring E k)
    {generatingJ generatingU : PartialEdgeColoring E k}
    {ettJ : ExtendedTashkinovTree G k e0 inputJ J generatingJ}
    {ettU : ExtendedTashkinovTree G k e0 inputU U generatingU}
    {baseJ : HierarchyBase ettJ sigma} {baseU : HierarchyBase ettU sigma}
    (KJ : TashkinovHierarchy ettJ baseJ) (goodJ : GoodHierarchy KJ)
    (KU : TashkinovHierarchy ettU baseU) (goodU : GoodHierarchy KU)
    (hgammaLast : ∀ eta : Fin k,
      goodU.gamma (Fin.last KU.dividerCount) eta =
        goodJ.gamma (Fin.last KJ.dividerCount) eta)
    (hterminal : HierarchyTerminalStoredColors KU ⊆
      HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount))
    (hnewMissing : ∀ eta : Fin k,
      eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) →
      eta ∉ HierarchyTerminalStoredColors KU →
      eta ∈ TreeMissingColors sigma U) :
    let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
    let restrictedColors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
      fun W eta => Finset.univ.filter fun c =>
        ∃ r : Fin W.length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
          sigma (W.edge r) = some c
    (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
      Disjoint (goodJ.gamma lastJ eta) (restrictedColors U eta)) →
    (∀ W : TreeSequence G e0,
      TashkinovAugmentation sigma U W →
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
        Disjoint (goodJ.gamma lastJ eta) (restrictedColors W eta)) →
      False) →
    TreeColorSetMinusClosed G sigma U
      ((HierarchyTerminalStoredColors KU).biUnion
        (goodU.gamma (Fin.last KU.dividerCount))) := by
  classical
  dsimp
  intro havoid hmaximal
  unfold TreeColorSetMinusClosed TreeColorSetClosed
  intro c hc
  obtain ⟨hcMissing, hcOutside⟩ := Finset.mem_sdiff.mp hc
  by_contra hboundary
  have hnonempty :
      (BoundaryColorEdges G sigma (TreeSequenceVertexSet U) c).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hboundary
  obtain ⟨f, hf⟩ := hnonempty
  obtain ⟨W, hAdjoin, hAugment, _⟩ :=
    BoundaryMissingColorAugmentation G k e0 sigma U c f hf hcMissing
  obtain ⟨hLength, hInitial, hLastEdge⟩ := hAdjoin
  apply hmaximal W hAugment
  intro eta heta
  apply Finset.disjoint_left.mpr
  intro x hxGamma hxRestricted
  rw [Finset.mem_filter] at hxRestricted
  obtain ⟨_, r, hrA, hrCutoff, hrColor⟩ := hxRestricted
  by_cases hetaTerminal : eta ∈ HierarchyTerminalStoredColors KU
  · have hetaLast := hterminal hetaTerminal
    have hcGammaU : c ∉ goodU.gamma (Fin.last KU.dividerCount) eta := by
      intro hcGamma
      apply hcOutside
      exact Finset.mem_biUnion.mpr ⟨eta, hetaTerminal, hcGamma⟩
    have hcGammaJ : c ∉ goodJ.gamma (Fin.last KJ.dividerCount) eta := by
      rw [← hgammaLast eta]
      exact hcGammaU
    have hCutoff := HierarchyFirstMissingPositionPrefixCutoff sigma U W
      hInitial eta U.length (le_refl U.length)
    by_cases hrOld : r.val < U.length
    · let rU : Fin U.length := ⟨r.val, hrOld⟩
      have hrCutoffU :
          rU.val < min (HierarchyFirstMissingPosition sigma U eta).val U.length := by
        rw [hCutoff]
        dsimp [rU]
        have hFirst := Nat.min_le_left
          (HierarchyFirstMissingPosition sigma W eta).val W.length
        omega
      have hrEdge : W.edge r = U.edge rU := by
        have hrCast : Fin.castLE hInitial.1 rU = r := Fin.ext rfl
        rw [← hrCast, hInitial.2.2 rU]
      have hxRestrictedU : x ∈ Finset.univ.filter (fun d =>
          ∃ s : Fin U.length,
            (HierarchyStarredStage KJ (Fin.last KJ.dividerCount)).length ≤ s.val ∧
              s.val < min (HierarchyFirstMissingPosition sigma U eta).val U.length ∧
              sigma (U.edge s) = some d) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ x, rU, hrA, hrCutoffU, hrEdge ▸ hrColor⟩
      exact (Finset.disjoint_left.mp (havoid eta hetaLast)) hxGamma hxRestrictedU
    · have hrLast : r.val = U.length := by
        have hrBound : r.val < U.length + 1 := by simpa [hLength] using r.isLt
        omega
      have hrEq : r = Fin.cast hLength.symm (Fin.last U.length) := by
        apply Fin.ext
        simp [hrLast]
      have hxEq : x = c := by
        rw [hrEq, hLastEdge] at hrColor
        have hfColor : sigma f = some c := by
          have hf' := hf
          change f ∈ (BoundaryEdges G (TreeSequenceVertexSet U)).filter
            (fun g => sigma g = some c) at hf'
          exact (Finset.mem_filter.mp hf').2
        exact Option.some.inj (hrColor.symm.trans hfColor)
      exact hcGammaJ (hxEq ▸ hxGamma)
  · have hetaMissing := hnewMissing eta heta hetaTerminal
    have hFirstWBound :
        (HierarchyFirstMissingPosition sigma W eta).val ≤ U.length := by
      exact TreeSequenceFirstMissingPositionLePrefix hInitial hetaMissing
    have hCutoff := HierarchyFirstMissingPositionPrefixCutoff sigma U W
      hInitial eta U.length (le_refl U.length)
    have hrOld : r.val < U.length := by
      omega
    let rU : Fin U.length := ⟨r.val, hrOld⟩
    have hrCutoffU :
        rU.val < min (HierarchyFirstMissingPosition sigma U eta).val U.length := by
      rw [hCutoff]
      dsimp [rU]
      have hFirst := Nat.min_le_left
        (HierarchyFirstMissingPosition sigma W eta).val W.length
      omega
    have hrEdge : W.edge r = U.edge rU := by
      have hrCast : Fin.castLE hInitial.1 rU = r := Fin.ext rfl
      rw [← hrCast, hInitial.2.2 rU]
    have hxRestrictedU : x ∈ Finset.univ.filter (fun d =>
        ∃ s : Fin U.length,
          (HierarchyStarredStage KJ (Fin.last KJ.dividerCount)).length ≤ s.val ∧
            s.val < min (HierarchyFirstMissingPosition sigma U eta).val U.length ∧
            sigma (U.edge s) = some d) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, rU, hrA, hrCutoffU, hrEdge ▸ hrColor⟩
    exact (Finset.disjoint_left.mp (havoid eta heta)) hxGamma hxRestrictedU

end GoldbergSeymour

end

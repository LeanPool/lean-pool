/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchyCommonOriginalBaseTransport
public import LeanPool.GoldbergSeymour.GoodHierarchyRestrictedEndpointMinusClosed
public import LeanPool.GoldbergSeymour.GoodHierarchySameDividerReconstruction
public import LeanPool.GoldbergSeymour.GoodHierarchySameDividerTransport

public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColorsSubsetLast

/-!
# Good Hierarchy Restricted Endpoint Reconstruction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchyRestrictedEndpointReconstruction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J U : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (goodJ : GoodHierarchy KJ)
    (corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U)
    (hJU : TashkinovAugmentationSequence sigma J U) :
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
    ∃ baseU : HierarchyBase corrU.replacementETT sigma,
      baseU.core = baseJ.core ∧
      baseU.closure = baseJ.closure ∧
      baseU.supportPosition.val = baseJ.supportPosition.val ∧
      ∃ KU : TashkinovHierarchy corrU.replacementETT baseU,
        ∃ hcount : KU.dividerCount = KJ.dividerCount,
          (∀ j : Fin (KU.dividerCount + 1),
            let jo : Fin (KJ.dividerCount + 1) :=
              Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
            KU.stage j.castSucc = KJ.stage jo.castSucc ∧
              HierarchyStarredStage KU j = HierarchyStarredStage KJ jo ∧
              HierarchyStoredColorsAt KU j =
                HierarchyStoredColorsAt KJ jo ∧
              HierarchyStageMissingColors KU j =
                HierarchyStageMissingColors KJ jo) ∧
          (∀ i : Fin KU.dividerCount,
            (KU.dividerPosition i).val =
              (KJ.dividerPosition (Fin.cast hcount i)).val) ∧
          ∃ goodU : GoodHierarchy KU,
            (∀ j : Fin (KU.dividerCount + 1),
              let jo : Fin (KJ.dividerCount + 1) :=
                Fin.cast (congrArg (fun n : ℕ => n + 1) hcount) j
              ∀ eta : Fin k,
                goodU.gamma j eta = goodJ.gamma jo eta) ∧
            HierarchyTerminalStoredColors KU ⊆
              HierarchyStoredColorsAt KJ lastJ ∧
            TreeColorSetMinusClosed G sigma U
              ((HierarchyTerminalStoredColors KU).biUnion
                (goodU.gamma (Fin.last KU.dividerCount))) := by
  classical
  dsimp
  intro havoid hmaximal
  obtain ⟨baseU, hcore, hclosure, hsupport⟩ :=
    GoodHierarchyCommonOriginalBaseTransport G k e0 input T generating sigma
      ett J U corrJ baseJ corrU
  obtain ⟨KU, hcount, hstages, hdividers⟩ :=
    GoodHierarchySameDividerReconstruction G k e0 input T generating sigma
      ett J U corrJ baseJ KJ corrU baseU hcore hJU
  obtain ⟨goodU, hgamma⟩ :=
    GoodHierarchySameDividerTransport G k e0 input T generating sigma ett J U
      corrJ baseJ KJ goodJ corrU baseU hcore hclosure KU hcount hstages hJU
      havoid
  have hlastStored :
      HierarchyStoredColorsAt KU (Fin.last KU.dividerCount) =
        HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) := by
    have h := (hstages (Fin.last KU.dividerCount)).2.2.1
    simpa using h
  have hstored : HierarchyTerminalStoredColors KU ⊆
      HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) := by
    intro eta heta
    rw [← hlastStored]
    exact (HierarchyTerminalStoredColorsSubsetLast KU).1 heta
  have hnewMissing :
    ∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) → eta ∉
        HierarchyTerminalStoredColors KU → eta ∈ TreeMissingColors sigma U := by
    intro eta heta hnot
    apply (HierarchyTerminalStoredColorsSubsetLast KU).2 eta
    · rw [hlastStored]
      exact heta
    · exact hnot
  have hgammaLast : ∀ eta : Fin k,
      goodU.gamma (Fin.last KU.dividerCount) eta =
        goodJ.gamma (Fin.last KJ.dividerCount) eta := by
    intro eta
    simpa using hgamma (Fin.last KU.dividerCount) eta
  have hminus :=
    GoodHierarchyRestrictedEndpointMinusClosed G k e0 J U sigma KJ goodJ KU
      goodU hgammaLast hstored hnewMissing
      havoid hmaximal
  exact ⟨baseU, hcore, hclosure, hsupport, KU, hcount, hstages,
    hdividers, goodU, hgamma, hstored, hminus⟩

end GoldbergSeymour

end

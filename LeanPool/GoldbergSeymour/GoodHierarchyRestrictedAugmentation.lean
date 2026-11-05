/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchyRestrictedEndpointReconstruction
public import LeanPool.GoldbergSeymour.GoodHierarchyRestrictedMaximalChain

public import LeanPool.GoldbergSeymour.RestrictedAugmentationCorrespondingEndpoint

/-!
# Good Hierarchy Restricted Augmentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem GoodHierarchyRestrictedAugmentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hmod : ModColoring ett sigma) (hMP : MaximumProperty ett)
    (J : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett sigma J)
    (baseJ : HierarchyBase corrJ.replacementETT sigma)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (goodJ : GoodHierarchy KJ) :
    let lastJ : Fin (KJ.dividerCount + 1) := Fin.last KJ.dividerCount
    let A : TreeSequence G e0 := HierarchyStarredStage KJ lastJ
    let restrictedColors : TreeSequence G e0 → Fin k → Finset (Fin k) :=
      fun W eta => Finset.univ.filter fun c =>
        ∃ r : Fin W.length, A.length ≤ r.val ∧
          r.val < min (HierarchyFirstMissingPosition sigma W eta).val W.length ∧
          sigma (W.edge r) = some c
    ∃ (m : ℕ) (chain : Fin (m + 1) → TreeSequence G e0)
        (U : TreeSequence G e0),
      chain 0 = J ∧ chain (Fin.last m) = U ∧
      (∀ r : Fin m,
        TashkinovAugmentation sigma (chain r.castSucc) (chain r.succ) ∧
          ∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
            Disjoint (goodJ.gamma lastJ eta)
              (restrictedColors (chain r.succ) eta)) ∧
      (∀ r : Fin (m + 1), (chain r).length = J.length + r.val) ∧
      (∀ r s : Fin (m + 1), r.val ≤ s.val →
        TreeSequenceInitialSegment (chain r) (chain s)) ∧
      (∀ r : Fin m,
        TreeSequenceVertexSet (chain r.castSucc) ⊂
          TreeSequenceVertexSet (chain r.succ)) ∧
      TashkinovAugmentationSequence sigma J U ∧
      (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
        Disjoint (goodJ.gamma lastJ eta) (restrictedColors U eta)) ∧
      (∀ W : TreeSequence G e0,
        TashkinovAugmentation sigma U W →
        (∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ lastJ →
          Disjoint (goodJ.gamma lastJ eta) (restrictedColors W eta)) →
        False) ∧
      ∃ corrU : CorrespondingExtendedTashkinovTree G k e0 ett sigma U,
        MaximumProperty corrU.replacementETT ∧
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
  obtain ⟨m, chain, U, hfirst, hlast, hsteps, hlengths, hsegments,
      hvertices, hsequence, havoid, hmaximal⟩ :=
    GoodHierarchyRestrictedMaximalChain G k e0 corrJ.replacementInput J sigma
      baseJ KJ goodJ
  obtain ⟨corrU, hMPU⟩ :=
    RestrictedAugmentationCorrespondingEndpoint G k e0 input T generating sigma
      ett hmod hMP J U corrJ hsequence
  obtain ⟨baseU, hcore, hclosure, hsupport, KU, hcount, hstages,
      hdividers, goodU, hgamma, hstored, hminus⟩ :=
    GoodHierarchyRestrictedEndpointReconstruction G k e0 input T generating
      sigma ett J U corrJ baseJ KJ goodJ corrU hsequence havoid hmaximal
  exact ⟨m, chain, U, hfirst, hlast, hsteps, hlengths, hsegments,
    hvertices, hsequence, havoid, hmaximal, corrU, hMPU, baseU, hcore,
    hclosure, hsupport, KU, hcount, hstages, hdividers, goodU, hgamma,
    hstored, hminus⟩

end GoldbergSeymour

end

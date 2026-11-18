/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

public import LeanPool.GoldbergSeymour.BoundaryMissingColorAugmentation
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.GoodHierarchy

/-!
# Algorithm Five Five Parallel Strict Growth

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem AlgorithmFiveFiveParallelStrictGrowth {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (J : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett phi J)
    (baseJ : HierarchyBase corrJ.replacementETT phi)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (goodJ : GoodHierarchy KJ)
    (hzero : KJ.dividerCount = 0)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hJcore : J = baseJ.core)
    (m : ℕ) (U : TreeSequence G e0)
    (hUlength : U.length = J.length + m)
    (hzeroEndpoint : m = 0 → U = J)
    (hmaximal : ∀ W : TreeSequence G e0,
      TashkinovAugmentation phi U W →
      (∀ eta : Fin k,
        eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) →
        Disjoint (goodJ.gamma (Fin.last KJ.dividerCount) eta)
          (Finset.univ.filter fun c =>
            ∃ r : Fin W.length,
              (HierarchyStarredStage KJ
                (Fin.last KJ.dividerCount)).length ≤ r.val ∧
              r.val < min (HierarchyFirstMissingPosition phi W eta).val
                W.length ∧
              phi (W.edge r) = some c)) →
      False) :
    J.length < U.length := by
  classical
  have hpeReplacement :
      corrJ.replacementETT.series.data.kind
          (Fin.last corrJ.replacementETT.rounds) =
        some TashkinovExtensionKind.PE := by
    exact corrJ.terminalData.2.1.trans hPE
  have hnot := (goodJ.parallelBase hpeReplacement).1
  have hlast : Fin.last KJ.dividerCount = 0 := by
    apply Fin.ext
    simp [hzero]
  have hstar :
      HierarchyStarredStage KJ (Fin.last KJ.dividerCount) = J := by
    rw [hlast]
    simp [HierarchyStarredStage, hJcore]
  let C := (HierarchyStoredColorsAt KJ 0).biUnion (goodJ.gamma 0)
  have hnotC : ¬ TreeColorSetMinusClosed G phi baseJ.core C := by
    simpa [C] using hnot
  change ¬ TreeColorSetClosed G phi baseJ.core
      (TreeMissingColors phi baseJ.core \ C) at hnotC
  simp only [TreeColorSetClosed] at hnotC
  push Not at hnotC
  rcases hnotC with ⟨c, hc, hboundary⟩
  have hcJ : c ∈ TreeMissingColors phi J := by
    have := (Finset.mem_sdiff.mp hc).1
    simpa [hJcore] using this
  have hcOutside : c ∉ C := (Finset.mem_sdiff.mp hc).2
  obtain ⟨f, hf⟩ := hboundary
  have hcolor : phi f = some c :=
    (Finset.mem_filter.mp (show f ∈ BoundaryColorEdges G phi
      (TreeSequenceVertexSet baseJ.core) c from hf)).2
  have hboundaryJ :
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet J) c := by
    simpa [hJcore] using hf
  obtain ⟨W, hAdjoin, hAugment, _⟩ :=
    BoundaryMissingColorAugmentation G k e0 phi J c f hboundaryJ hcJ
  rcases hAdjoin with ⟨hlen, hInitial, hLastEdge⟩
  have hwindow :
    ∀ eta : Fin k, Finset.univ.filter (fun d =>
    ∃ r : Fin W.length, (HierarchyStarredStage KJ (Fin.last KJ.dividerCount)).length ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi W eta).val W.length ∧ phi (W.edge r) = some
        d) ⊆ {c} := by
    intro eta d hd
    rcases (Finset.mem_filter.mp hd).2 with ⟨r, hrlo, hrhi, hphi⟩
    have hrval : r.val = J.length := by
      rw [hstar] at hrlo
      have hrlt : r.val < W.length := lt_of_lt_of_le hrhi (min_le_right _ _)
      omega
    have hr : r = Fin.cast hlen.symm (Fin.last J.length) := by
      apply Fin.ext
      simp [hrval]
    rw [hr, hLastEdge] at hphi
    have hcolor' : phi f = some c := hcolor
    rw [hcolor'] at hphi
    exact Finset.mem_singleton.mpr (Option.some.inj hphi.symm)
  have hdisjoint :
    ∀ eta : Fin k, eta ∈ HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) → Disjoint
        (goodJ.gamma (Fin.last KJ.dividerCount) eta) (Finset.univ.filter fun d =>
    ∃ r : Fin W.length, (HierarchyStarredStage KJ (Fin.last KJ.dividerCount)).length ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi W eta).val W.length ∧ phi (W.edge r) = some
        d) := by
    intro eta heta
    apply Finset.disjoint_left.mpr
    intro d hdGamma hdWindow
    rw [hlast] at hdGamma
    have hdC : d ∈ C := by
      apply Finset.mem_biUnion.mpr
      refine ⟨eta, ?_, hdGamma⟩
      simpa [hlast] using heta
    have hdc : d = c := Finset.mem_singleton.mp (hwindow eta hdWindow)
    subst d
    exact hcOutside hdC
  by_contra hstrict
  have hm : m = 0 := by omega
  have hUeq := hzeroEndpoint hm
  exact hmaximal W (by simpa [hUeq] using hAugment) hdisjoint

end GoldbergSeymour

end

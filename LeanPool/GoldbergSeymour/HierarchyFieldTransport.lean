/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.SameHierarchyStages
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff

/-!
# Transport of hierarchy fields

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Segment colors can only shrink when a hierarchy stage is cut to a color-preserving prefix. -/
theorem TashkinovHierarchy.segmentColors_subset_of_prefix
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input input' phi mu generating generating' : PartialEdgeColoring E k}
    {T C : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {ett' : ExtendedTashkinovTree G k e0 input' C generating'}
    {base : HierarchyBase ett phi} {base' : HierarchyBase ett' mu}
    (H : TashkinovHierarchy ett base) (K : TashkinovHierarchy ett' base')
    (j : Fin (H.dividerCount + 1)) (j' : Fin (K.dividerCount + 1)) (eta : Fin k)
    (hstar : HierarchyStarredStage K j' = HierarchyStarredStage H j)
    (hUW : TreeSequenceInitialSegment (K.stage j'.succ) (H.stage j.succ))
    (hUC : TreeSequenceInitialSegment (K.stage j'.succ) C)
    (hCT : TreeSequenceInitialSegment C T)
    (hfirst : (HierarchyFirstMissingPosition mu C eta).val =
      (HierarchyFirstMissingPosition phi C eta).val)
    (hfixed : ∀ r : Fin C.length, mu (C.edge r) = phi (C.edge r)) :
    HierarchySegmentColors K j' eta ⊆ HierarchySegmentColors H j eta := by
  classical
  have hcut : min (HierarchyFirstMissingPosition mu C eta).val
      (K.stage j'.succ).length =
      min (HierarchyFirstMissingPosition phi T eta).val (K.stage j'.succ).length := by
    rw [hfirst]
    exact HierarchyFirstMissingPositionPrefixCutoff phi C T hCT eta _ hUC.1
  intro c hc
  simp only [HierarchySegmentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  obtain ⟨r, hlo, hhi, hcol⟩ := hc
  refine ⟨Fin.castLE hUW.1 r, ?_, ?_, ?_⟩
  · simpa only [hstar, Fin.val_castLE] using hlo
  · have hr : r.val < (HierarchyFirstMissingPosition phi T eta).val := by
      rw [hcut] at hhi
      exact lt_of_lt_of_le hhi (Nat.min_le_left _ _)
    exact lt_min hr (Fin.castLE hUW.1 r).isLt
  · rw [hUW.2.2 r]
    have hf := hfixed (Fin.castLE hUC.1 r)
    rw [hUC.2.2 r] at hf
    exact hf.symm.trans hcol

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input otherInput generating otherGenerating phi sigma : PartialEdgeColoring E k}
    {T U : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {otherETT : ExtendedTashkinovTree G k e0 otherInput U otherGenerating}
    {base : HierarchyBase ett phi} {otherBase : HierarchyBase otherETT sigma}

/-- Stored colors transport through terminal stored-color and starred-stage agreement. -/
theorem TashkinovHierarchy.storedColors_eq_of_agreement
    (original : TashkinovHierarchy ett base) (replacement : TashkinovHierarchy otherETT otherBase)
    (i : Fin (original.dividerCount + 1)) (j : Fin (replacement.dividerCount + 1))
    (stored : TashkinovStoredColors otherETT.series.data (Fin.last otherETT.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
    (star : HierarchyStarredStage replacement j = HierarchyStarredStage original i)
    (missing : TreeMissingColors sigma (HierarchyStarredStage original i) =
      TreeMissingColors phi (HierarchyStarredStage original i)) :
    HierarchyStoredColorsAt replacement j = HierarchyStoredColorsAt original i := by
  unfold HierarchyStoredColorsAt
  dsimp only
  rw [stored, star, missing]

/-- The ladder-base case is the zeroth ordinary stage as well. -/
theorem TashkinovHierarchy.stageMissingColors_eq (hierarchy : TashkinovHierarchy ett base)
    (i : Fin (hierarchy.dividerCount + 1)) :
    HierarchyStageMissingColors hierarchy i =
      TreeMissingColors phi (hierarchy.stage i.castSucc) := by
  refine Fin.cases ?_ (fun _ => rfl) i
  change TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
    TreeMissingColors phi (hierarchy.stage 0)
  rw [hierarchy.baseStage]

/-- Stage missing colors depend only on the actual stage and its missing-color sets. -/
theorem TashkinovHierarchy.stageMissingColors_eq_of_agreement
    (original : TashkinovHierarchy ett base) (replacement : TashkinovHierarchy otherETT otherBase)
    (i : Fin (original.dividerCount + 1)) (j : Fin (replacement.dividerCount + 1))
    (stage : replacement.stage j.castSucc = original.stage i.castSucc)
    (missing : TreeMissingColors sigma (original.stage i.castSucc) =
      TreeMissingColors phi (original.stage i.castSucc)) :
    HierarchyStageMissingColors replacement j = HierarchyStageMissingColors original i := by
  rw [replacement.stageMissingColors_eq, original.stageMissingColors_eq, stage, missing]

/-- Segment colors transport through tree, first-position and edge-color agreement. -/
theorem TashkinovHierarchy.segmentColors_eq_of_agreement
    (original : TashkinovHierarchy ett base) (replacement : TashkinovHierarchy otherETT otherBase)
    (i : Fin (original.dividerCount + 1)) (j : Fin (replacement.dividerCount + 1)) (eta : Fin k)
    (stage : replacement.stage j.succ = original.stage i.succ)
    (star : HierarchyStarredStage replacement j = HierarchyStarredStage original i)
    (first : (HierarchyFirstMissingPosition sigma U eta).val =
      (HierarchyFirstMissingPosition phi T eta).val)
    (edges : ∀ index : Fin (original.stage i.succ).length,
      sigma ((original.stage i.succ).edge index) = phi ((original.stage i.succ).edge index)) :
    HierarchySegmentColors replacement j eta = HierarchySegmentColors original i eta := by
  unfold HierarchySegmentColors
  rw [stage]
  simp only [star, first, edges]

/-- Missing colors on a hierarchy increment transport through actual stage agreement. -/
theorem TashkinovHierarchy.segmentMissingColors_eq_of_agreement
    (original : TashkinovHierarchy ett base) (replacement : TashkinovHierarchy otherETT otherBase)
    (i : Fin original.dividerCount) (j : Fin replacement.dividerCount)
    (stage : replacement.stage j.succ.castSucc = original.stage i.succ.castSucc)
    (star : HierarchyStarredStage replacement j.castSucc =
      HierarchyStarredStage original i.castSucc)
    (missing : ∀ vertex ∈ TreeSequenceVertexSet (original.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage original i.castSucc),
      MissingColors G sigma vertex = MissingColors G phi vertex) :
    ((TreeSequenceVertexSet (replacement.stage j.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage replacement j.castSucc)).biUnion
      (MissingColors G sigma)) =
    ((TreeSequenceVertexSet (original.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage original i.castSucc)).biUnion
      (MissingColors G phi)) := by
  rw [stage, star]
  exact Finset.biUnion_congr rfl missing

/-- Agreement of indexed starred stages identifies the final starred stage. -/
theorem TashkinovHierarchy.lastStarredStage_eq_of_agreement
    (original : TashkinovHierarchy ett base) (replacement : TashkinovHierarchy otherETT otherBase)
    (count : replacement.dividerCount = original.dividerCount)
    (stars : ∀ index : Fin (replacement.dividerCount + 1),
      HierarchyStarredStage replacement index = HierarchyStarredStage original
        (Fin.cast (congrArg (fun n : ℕ => n + 1) count) index)) :
    HierarchyStarredStage replacement (Fin.last replacement.dividerCount) =
      HierarchyStarredStage original (Fin.last original.dividerCount) := by
  have lastIndex : Fin.cast (congrArg (fun n : ℕ => n + 1) count)
      (Fin.last replacement.dividerCount) = Fin.last original.dividerCount := Fin.ext count
  simpa only [lastIndex] using stars (Fin.last replacement.dividerCount)

/-- The unique-refresh predicate transports without reconstructing either hierarchy. -/
theorem GoodHierarchy.uniqueRefresh_transport {original : TashkinovHierarchy ett base}
    (good : GoodHierarchy original) (replacement : TashkinovHierarchy otherETT otherBase)
    (i : Fin original.dividerCount) (j : Fin replacement.dividerCount)
    (stored : HierarchyStoredColorsAt replacement j.succ = HierarchyStoredColorsAt original i.succ)
    (stage : replacement.stage j.succ.castSucc = original.stage i.succ.castSucc)
    (star : HierarchyStarredStage replacement j.castSucc =
      HierarchyStarredStage original i.castSucc)
    (missing : ∀ vertex ∈ TreeSequenceVertexSet (original.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage original i.castSucc),
      MissingColors G sigma vertex = MissingColors G phi vertex) :
    ∃! eta : Fin k, eta ∈ HierarchyStoredColorsAt replacement j.succ ∧
      good.gamma i.succ eta ⊆
        ((TreeSequenceVertexSet (replacement.stage j.succ.castSucc) \
            TreeSequenceVertexSet (HierarchyStarredStage replacement j.castSucc)).biUnion
          (MissingColors G sigma)) ∧
      ∀ theta ∈ HierarchyStoredColorsAt replacement j.succ, theta ≠ eta →
        good.gamma i.succ theta = good.gamma i.castSucc theta := by
  rw [stored, original.segmentMissingColors_eq_of_agreement replacement i j stage star missing]
  exact good.uniqueRefresh i

variable {original : TashkinovHierarchy ett base}

/-- Auxiliary color families use the canonical backward cast of divider indices. -/
def GoodHierarchy.reindexedGamma (good : GoodHierarchy original)
    (replacement : TashkinovHierarchy otherETT otherBase)
    (count : original.dividerCount = replacement.dividerCount) :
    Fin (replacement.dividerCount + 1) → Fin k → Finset (Fin k) :=
  fun index => good.gamma (Fin.cast (congrArg (fun value => value + 1) count.symm) index)

/-- Transport the common fields of a good hierarchy; closure obligations stay explicit. -/
noncomputable def GoodHierarchy.transportOfFields (good : GoodHierarchy original)
    (replacement : TashkinovHierarchy otherETT otherBase)
    (count : original.dividerCount = replacement.dividerCount)
    (stored : ∀ index, HierarchyStoredColorsAt replacement index = HierarchyStoredColorsAt original
      (Fin.cast (congrArg (fun value => value + 1) count.symm) index))
    (missing : ∀ index, HierarchyStageMissingColors replacement index =
      HierarchyStageMissingColors original
        (Fin.cast (congrArg (fun value => value + 1) count.symm) index))
    (segment : ∀ index color, color ∈ HierarchyStoredColorsAt original
        (Fin.cast (congrArg (fun value => value + 1) count.symm) index) →
      HierarchySegmentColors replacement index color ⊆ HierarchySegmentColors original
        (Fin.cast (congrArg (fun value => value + 1) count.symm) index) color)
    (refresh : ∀ index : Fin replacement.dividerCount,
      ((TreeSequenceVertexSet (replacement.stage index.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage replacement index.castSucc)).biUnion
        (MissingColors G sigma)) =
      ((TreeSequenceVertexSet (original.stage (Fin.cast count.symm index).succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage original
            (Fin.cast count.symm index).castSucc)).biUnion (MissingColors G phi)))
    (parallel : otherETT.series.data.kind (Fin.last otherETT.rounds) =
        some TashkinovExtensionKind.PE →
      ¬TreeColorSetMinusClosed G sigma otherBase.core
          ((HierarchyStoredColorsAt replacement 0).biUnion
            (good.reindexedGamma replacement count 0)) ∧
        4 ≤ ((TreeMissingColors sigma (otherETT.series.data.tree
          (Fin.last otherETT.rounds).castSucc) ∩ TreeMissingColors sigma otherBase.closure) \
          (HierarchyStoredColorsAt replacement 0).biUnion
            (good.reindexedGamma replacement count 0)).card)
    (minus : ∀ index : Fin replacement.dividerCount,
      TreeColorSetMinusClosed G sigma (replacement.stage index.succ.castSucc)
        ((HierarchyStoredColorsAt replacement index.succ).biUnion
          (good.reindexedGamma replacement count index.castSucc))) :
    GoodHierarchy replacement where
  gamma := good.reindexedGamma replacement count
  twoColors := by
    intro index color member
    exact good.twoColors _ color (stored index ▸ member)
  avoidance := by
    intro index color member other inGamma
    have old := good.avoidance _ color (stored index ▸ member) inGamma
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · rw [missing]
      exact (Finset.mem_sdiff.mp old).1
    · intro inSegment
      exact (Finset.mem_sdiff.mp old).2 (segment index color (stored index ▸ member) inSegment)
  disjointPairs := by
    intro index color other member otherMember different
    exact good.disjointPairs _ color other (stored index ▸ member)
      (stored index ▸ otherMember) different
  uniqueRefresh := by
    intro index
    simpa only [reindexedGamma, stored, refresh, Fin.cast_succ_eq, Fin.cast_castSucc] using
      good.uniqueRefresh (Fin.cast count.symm index)
  parallelBase := parallel
  minusClosed := minus

section CommonTerminalTree

variable {alignedETT : ExtendedTashkinovTree G k e0 otherInput T otherGenerating}
    {alignedBase : HierarchyBase alignedETT sigma}

/-- Recolor a good hierarchy using local color agreement and explicit closure obligations. -/
noncomputable def GoodHierarchy.transportOfColoringAgreement (good : GoodHierarchy original)
    (replacement : TashkinovHierarchy alignedETT alignedBase)
    (same : SameHierarchyStages original replacement)
    (stored : TashkinovStoredColors alignedETT.series.data (Fin.last alignedETT.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
    (stageMissing : ∀ index : Fin (original.dividerCount + 1),
      TreeMissingColors sigma (original.stage index.castSucc) =
        TreeMissingColors phi (original.stage index.castSucc))
    (starMissing : ∀ index : Fin (original.dividerCount + 1),
      TreeMissingColors sigma (HierarchyStarredStage original index) =
        TreeMissingColors phi (HierarchyStarredStage original index))
    (first : ∀ (index : Fin (original.dividerCount + 1)) (color : Fin k),
      color ∈ HierarchyStoredColorsAt original index →
      (HierarchyFirstMissingPosition sigma T color).val =
        (HierarchyFirstMissingPosition phi T color).val)
    (edges : ∀ (index : Fin (original.dividerCount + 1))
      (position : Fin (original.stage index.succ).length),
      sigma ((original.stage index.succ).edge position) =
        phi ((original.stage index.succ).edge position))
    (vertexMissing : ∀ index : Fin original.dividerCount,
      ∀ vertex ∈ TreeSequenceVertexSet (original.stage index.succ.castSucc) \
          TreeSequenceVertexSet (HierarchyStarredStage original index.castSucc),
        MissingColors G sigma vertex = MissingColors G phi vertex)
    (parallel : ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
      ¬TreeColorSetMinusClosed G sigma base.core
          ((HierarchyStoredColorsAt original 0).biUnion (good.gamma 0)) ∧
        4 ≤ ((TreeMissingColors sigma (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
          TreeMissingColors sigma base.closure) \
          (HierarchyStoredColorsAt original 0).biUnion (good.gamma 0)).card)
    (minus : ∀ index : Fin original.dividerCount,
      TreeColorSetMinusClosed G sigma (original.stage index.succ.castSucc)
        ((HierarchyStoredColorsAt original index.succ).biUnion (good.gamma index.castSucc))) :
    GoodHierarchy replacement := by
  have storedEq (index : Fin (replacement.dividerCount + 1)) :
      HierarchyStoredColorsAt replacement index = HierarchyStoredColorsAt original
        (Fin.cast (congrArg (fun count => count + 1) same.2.1.symm) index) :=
    original.storedColors_eq_of_agreement replacement _ index stored
      (same.starredStage_eq index) (starMissing _)
  refine good.transportOfFields replacement same.2.1 storedEq ?_ ?_ ?_ ?_ ?_
  · intro index
    apply original.stageMissingColors_eq_of_agreement replacement _ index
    · simpa only [Fin.cast_castSucc] using same.stage_eq index.castSucc
    · exact stageMissing _
  · intro index color member
    apply Eq.subset
    apply original.segmentColors_eq_of_agreement replacement _ index color
    · simpa only [Fin.cast_succ_eq] using same.stage_eq index.succ
    · exact same.starredStage_eq index
    · exact first _ color member
    · exact edges _
  · intro index
    apply original.segmentMissingColors_eq_of_agreement replacement _ index
    · simpa only [Fin.cast_castSucc, Fin.cast_succ_eq] using
        same.stage_eq index.succ.castSucc
    · simpa only [Fin.cast_castSucc] using same.starredStage_eq index.castSucc
    · exact vertexMissing _
  · intro isParallel
    have originalParallel := same.2.2.2.2.1.mpr isParallel
    have treeEq : alignedETT.series.data.tree (Fin.last alignedETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
      rw [← replacement.baseStage, ← original.baseStage]
      simpa only [Fin.cast_zero] using same.stage_eq 0
    dsimp only [reindexedGamma]
    rw [Fin.cast_zero, storedEq, Fin.cast_zero, ← same.1,
      ← same.2.2.2.2.2 originalParallel, treeEq]
    exact parallel originalParallel
  · intro index
    dsimp only [reindexedGamma]
    rw [storedEq, same.stage_eq]
    simpa only [Fin.cast_succ_eq, Fin.cast_castSucc] using
      minus (Fin.cast same.2.1.symm index)

end CommonTerminalTree

end GoldbergSeymour

end

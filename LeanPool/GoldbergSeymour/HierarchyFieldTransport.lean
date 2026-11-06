/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy

/-!
# Transport of hierarchy fields

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

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

end GoldbergSeymour

end

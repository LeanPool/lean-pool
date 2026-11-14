/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase

/-!
# Elementarity at the penultimate certified stage

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Lower-round elementarity applies to the last ladder tree of a maximum certified series. -/
theorem ExtendedTashkinovTree.penultimateElementary {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} (ett : ExtendedTashkinovTree G k e0 input T phi)
    (maximum : MaximumProperty ett)
    (lower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (i : Fin ett.rounds) (last : Fin.last ett.rounds = i.succ) :
    ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
  classical
  have positive := ett.roundsPositive
  have indexValue : ett.rounds = i.val + 1 := congrArg Fin.val last
  intro u hu v hv different
  by_cases one : ett.rounds = 1
  · have zero : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    have base : ColoredVertexSetElementary G (ett.series.data.coloring 0)
        (TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩)) :=
      (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    have firstU : u ∈ TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩) := by
      simpa [zero, one] using hu
    have firstV : v ∈ TreeSequenceVertexSet (ett.series.data.tree ⟨1, by omega⟩) := by
      simpa [zero, one] using hv
    have firstColor : i.castSucc = (0 : Fin (ett.rounds + 1)) := Fin.ext (by simp [zero])
    rw [firstColor]
    exact base firstU firstV different
  · obtain ⟨restricted, rounds, restrictedMaximum, _, _⟩ :=
      CertifiedETTRestriction G k e0 input T phi ett maximum
        (ett.rounds - 1) (by omega) (by omega)
    have previous : ColoredVertexSetElementary G
        (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
        (TreeSequenceVertexSet (ett.series.data.tree ⟨ett.rounds - 1 + 1, by omega⟩)) :=
      (lower (lower := restricted) (by omega) (by omega) restrictedMaximum).1
    have colorIndex : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = i.castSucc :=
      Fin.ext (by simp; omega)
    have treeIndex : (⟨ett.rounds - 1 + 1, by omega⟩ : Fin (ett.rounds + 2)) =
        i.succ.castSucc := Fin.ext (by simp; omega)
    rw [colorIndex, treeIndex] at previous
    exact previous hu hv different

end GoldbergSeymour

end

/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.HierarchyStoredColorsAt

public import LeanPool.GoldbergSeymour.TreeColoringInvariant

/-!
# Hierarchy Weakly Stable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Base stability, together with invariance on the relevant hierarchy stage when the index is
positive.
-/
def HierarchyWeaklyStable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
  {T : TreeSequence G e0} {generating phi : PartialEdgeColoring E k}
  {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett phi}
  (H : TashkinovHierarchy ett base) (j : Fin (H.dividerCount + 1))
  (sigma : PartialEdgeColoring E k) : Prop :=
 let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
 let Tn := ett.series.data.tree n.castSucc
 let Dn := TashkinovStoredColors ett.series.data n
 let baseStable :=
  if ett.series.data.kind n = some TashkinovExtensionKind.PE then
   CombinedStableColoring Tn base.closure Dn phi sigma
  else StableColoring Tn Dn phi sigma
 Fin.cases baseStable
  (fun i : Fin H.dividerCount =>
   baseStable ∧ TreeColoringInvariant (H.stage i.succ.castSucc) phi sigma)
  j

end GoldbergSeymour

end

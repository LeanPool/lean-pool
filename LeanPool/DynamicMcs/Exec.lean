/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Definitions
public import LeanPool.DynamicMcs.GreedySearch

/-!
# Executable maximum-cardinality search

The greedy search uses Boolean adjacency rows and chooses the least index when
neighbor counts tie. A single-edge update changes the two symmetric entries.
-/

@[expose] public section

namespace DynamicMcs

namespace Exec

@[inherit_doc DynamicMcs.atRow]
abbrev atRow := @DynamicMcs.atRow

@[inherit_doc DynamicMcs.getAdj]
abbrev getAdj := @DynamicMcs.getAdj

@[inherit_doc DynamicMcs.cardC]
abbrev cardC := @DynamicMcs.cardC

@[inherit_doc DynamicMcs.bestPick]
abbrev bestPick := @DynamicMcs.bestPick

@[inherit_doc DynamicMcs.mcsStep]
abbrev mcsStep := @DynamicMcs.mcsStep

@[inherit_doc DynamicMcs.mcsOrder]
abbrev mcsOrder := @DynamicMcs.mcsOrder

@[inherit_doc DynamicMcs.setEdge]
abbrev setEdge := @DynamicMcs.setEdge

@[inherit_doc DynamicMcs.insertEdge]
abbrev insertEdge := @DynamicMcs.insertEdge

@[inherit_doc DynamicMcs.deleteEdge]
abbrev deleteEdge := @DynamicMcs.deleteEdge

@[inherit_doc DynamicMcs.toUGraph]
abbrev toUGraph := @DynamicMcs.toUGraph

end Exec
end DynamicMcs

/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/

module

public import LeanPool.RamseyReservoir.Bireservoir
public import LeanPool.RamseyReservoir.Book
public import LeanPool.RamseyReservoir.HomogeneousBlocks
public import LeanPool.RamseyReservoir.RamseyBound
public import LeanPool.RamseyReservoir.Reservoir

/-!
# Reservoir and book calculus for greedy Ramsey arguments

Source: url:https://github.com/Egly443/lean-ramsey-reservoir
Authors: Brian Sanders
Status: verified
Main declarations: `SimpleGraph.ramseyBound_of_pascal`, `SimpleGraph.ramseyNumber_three_three`,
  `SimpleGraph.sum_card_commonNeighbors_eq`, `SimpleGraph.ContainsBook.not_cliqueFree_or`,
  `SimpleGraph.HomogeneousBlocks.isNClique_anchor`
Tags: ramsey-theory, book-graphs, greedy-algorithms, extremal-graph-theory
MSC: 05C55, 05C35, 05D10
-/

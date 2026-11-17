/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/

/-!
# Weight shifting and extremal graph theory

Source: url:https://github.com/Egly443/lean-graph-extremal
Authors: Brian Sanders
Status: verified
Main declarations: `SimpleGraph.exists_isClique_support_le`,
  `SimpleGraph.cliqueWeight_le_choose_mul`, `SimpleGraph.paleyGraph_isSRGWith`
Tags: extremal-graph-theory, weight-shifting, paley-graphs
MSC: 05C55, 05D10
-/

module

public import LeanPool.GraphExtremal.Extremal.MotzkinStraus
public import LeanPool.GraphExtremal.Extremal.WeightShifting
public import LeanPool.GraphExtremal.Extremal.Zykov
public import LeanPool.GraphExtremal.Konig
public import LeanPool.GraphExtremal.LexProd
public import LeanPool.GraphExtremal.Paley

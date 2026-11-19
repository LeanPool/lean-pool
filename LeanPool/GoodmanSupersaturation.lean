/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/

module

public import LeanPool.GoodmanSupersaturation.Goodman
public import LeanPool.GoodmanSupersaturation.RamseyNumber
public import LeanPool.GoodmanSupersaturation.Supersaturation

/-!
# Goodman's formula and clique supersaturation for two-colourings

Source: url:https://github.com/Egly443/lean-goodman-supersaturation
Authors: Brian Sanders
Status: verified
Main declarations: `SimpleGraph.goodman_within`, `SimpleGraph.goodman_bound`,
  `SimpleGraph.IsRegularOfDegree.goodman_eq`, `SimpleGraph.supersaturation`,
  `SimpleGraph.choose_le_card_cliqueFinset_add_mul_choose_ramseyNumber`
Tags: ramsey-theory, extremal-graph-theory, supersaturation, combinatorics
MSC: 05C55, 05C35, 05D10
-/

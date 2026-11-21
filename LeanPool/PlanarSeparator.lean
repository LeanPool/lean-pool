/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: project entry point. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Main

/-!
# Planar separators and nested dissection

Source: doi:10.1137/0136016, url:https://github.com/RBarish-UTokyo/PlanarSeparator-NestedDissection-WordRAM-Lean4/tree/0b5373fd782ef11c5b049f03fa69506948092c05
Authors: Robert D. Barish
Status: verified
Main declarations: `PlanarSeparator.separator_theorem`, `PlanarSeparator.separator_theorem_induced`,
  `PlanarSeparator.sepTree_exists`, `PlanarSeparator.square_sepTree_exists`,
  `PlanarSeparator.fill_bound`, `PlanarSeparator.planar_nested_dissection`,
  `PlanarSeparator.square_nested_dissection`, `PlanarSeparator.separator_machine`
Tags: planar-graphs, graph-separators, nested-dissection, verified-complexity
MSC: 05C10, 05C85, 65F50, 68Q25
-/

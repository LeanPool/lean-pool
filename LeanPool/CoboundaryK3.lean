/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/

module

public import LeanPool.CoboundaryK3.Basic
public import LeanPool.CoboundaryK3.Constant
public import LeanPool.CoboundaryK3.Replication
public import LeanPool.CoboundaryK3.Staircase

/-!
# The Sym(3) permutation coboundary constant of the complete complex

Source: doi:10.5281/zenodo.23245792, url:https://github.com/dicipler-pixel/coboundary-k3-lean/tree/70a2b3de40f88f3bbe25b63e581e1fc84e88d841
Authors: Jeromie Beasley
Status: verified
Main declarations: `CoboundaryK3.h1_eq_all`, `CoboundaryK3.k_div_three_le_h1`,
  `CoboundaryK3.stair_gaugeDist`, `CoboundaryK3.h1_eq_four_mul`, `CoboundaryK3.witness_k8`
Tags: coboundary-expansion, cocycles, symmetric-group, complete-complex, kernel-decision
MSC: 05E45, 20B30, 55U10
-/

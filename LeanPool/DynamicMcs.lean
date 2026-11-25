/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Stability

/-!
# Dynamic maximum cardinality search

Source: arxiv:2611.18369, url:https://github.com/thonmay/mcs-lean/tree/0d0ddffbcef5817c50a073a350428edd2da5bfb5
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
Status: verified
Main declarations: `DynamicMcs.Proofs.common_order_extends_prefix`,
  `DynamicMcs.Proofs.insert_break_iff_old`, `DynamicMcs.Proofs.exec_insert_update_eq_mcsOrder`,
  `DynamicMcs.Proofs.exec_delete_update_eq_mcsOrder`, `DynamicMcs.Proofs.exec_insert_cost_le`,
  `DynamicMcs.Proofs.exec_delete_cost_of_no_break`
Tags: graph-algorithms, maximum-cardinality-search, dynamic-algorithms
MSC: 05C85, 68W40
-/

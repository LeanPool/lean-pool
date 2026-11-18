/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.FlatRun

/-!
# Verified worst-case constant-step order maintenance

Source: arxiv:2610.38616, url:https://github.com/dfirsov/order_maintenance/tree/312b7b7d0686550ce7106fff1f6a47acb3e72866
Authors: Denis Firsov
Status: verified
Main declarations: `OrderMaintenance.Impl.theoremAB_word`,
  `OrderMaintenance.Impl.theoremAB_flat_word`, `OrderMaintenance.Zeroing.zeroing`
Tags: data-structures, order-maintenance, verified-complexity, word-ram
MSC: 68P05, 68Q60
-/

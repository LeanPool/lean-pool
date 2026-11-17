/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.InsStart
public import LeanPool.OrderMaintenance.Proof.Top.Step


/-!
# M5: the top structure's contract

`TopInv`, `topMu` and the job bound `topJ` satisfy M4's contract, relative to `SDOK`
(a drain's start keeps the invariant).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof

/-- **The top structure's contract** (relative to the drain start, `SDOK`). -/
theorem topContract (hSD : SDOK) : TopContractP TopInv topMu topJ capT :=
  ⟨fun _ _ h hI => h.topInv hI, fun _ _ h => h.topMu,
    fun _ _ _ hA hT hres hx _ hcap => top_start hA hT hres hx hcap,
    fun _ _ _ _ hT hres => top_step hSD hT hres⟩

end OrderMaintenance.Proof.Top

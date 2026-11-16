/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.StartTime
public import LeanPool.OrderMaintenance.Proof.Top.Contract


/-!
# M5: a drain's start keeps the invariant

`startDrain` runs, keeps the core outside the top structure (`TopRel`), and its result
satisfies the invariant with the job moved to `afterDrain`: this is `SDOK`, so the top
structure's contract holds unconditionally.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof

/-- **A drain's start keeps the invariant.** -/
theorem sdOK : SDOK := by
  intro s cl ord dr n0 j v hpc hv0 hTP hCL hI hlp _ hof hW
  obtain ⟨side, hside, hlook⟩ := sp_side hpc hv0 hI hlp hTP hof hW
  have C : SDCtx s cl ord dr n0 j v side :=
    ⟨hpc, hv0, hI, hlp, hTP, hof, hW, hside, fun c hc => ((hCL.2 c).mp hc).1, hlook⟩
  have hvn := SDCtx.nN (s := s) v C.vl.1
  refine ⟨_, _, _, _, sr_run hpc hv0 hI hlp hTP hof hW hside hlook,
    sr_topRel hpc hv0 hI hlp hTP hof hW hside hlook, C.inv, ?_⟩
  rw [C.ht v, ite_eq_right (fun h => h.elim hvn.1 hvn.2)]

/-- **The top structure's contract.** -/
theorem topContract' : TopContractP TopInv topMu topJ capT := topContract sdOK

end OrderMaintenance.Proof.Top

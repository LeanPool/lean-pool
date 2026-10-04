/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport

/-! NF weak partition development: NominalAlphaOprabCompactSupport001. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.DirectNominalPrf.Nominal

/-! A closed structural reflexivity certificate for the three self-paired
binders and one genuinely renamed binder used by `df-oprab`. -/


/-- Checked nominal proof certificate identified upstream as `nb049_reflOn_self3_fresh`. -/
@[expose]
def nb049ReflOnSelf3Fresh (x : Var) (y : Var) (z : Var) (a : Var) (w : Var)
    (support : Finset Var) (ha : a ∉ support) (hw : w ∉ support) :
    TReflOn [(z, z), (y, y), (x, x), (a, w)] support :=
  by
  apply TEnvFresh.reflOn
  intro u v huv huv_ne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at huv
  rcases huv with huv | huv | huv | huv
  · cases huv
    exact (huv_ne rfl).elim
  · cases huv
    exact (huv_ne rfl).elim
  · cases huv
    exact (huv_ne rfl).elim
  · cases huv
    exact ⟨ha, hw⟩

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

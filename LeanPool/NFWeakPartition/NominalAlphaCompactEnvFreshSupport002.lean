/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport

/-! NF weak partition development: NominalAlphaCompactEnvFreshSupport002. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open NFChoice.DirectNominalPrf.Nominal

/-! Type-explicit successor to the compact `TEnvFresh` constructors.

`NFChoice.Foundation.Var` and `NFChoice.SemanticCore.Var` are distinct names
in this import context.  Every occurrence below is therefore qualified with
the exact variable type used by `TBinderEnv` and `TEnvFresh`. -/


namespace TEnvFresh

theorem nil (support : Finset NFChoice.SemanticCore.Var) : TEnvFresh [] support :=
  by
  intro x y hmem hne
  simp only [List.not_mem_nil] at hmem

theorem consSame {env : TBinderEnv} {support : Finset NFChoice.SemanticCore.Var}
    (x : NFChoice.SemanticCore.Var) (tail : TEnvFresh env support) :
    TEnvFresh ((x, x) :: env) support :=
  by
  intro a b hmem hne
  simp only [List.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · cases hmem
    exact (hne rfl).elim
  · exact tail hmem hne

theorem consFresh {env : TBinderEnv} {support : Finset NFChoice.SemanticCore.Var}
    (x : NFChoice.SemanticCore.Var) (y : NFChoice.SemanticCore.Var) (hx : x ∉ support)
    (hy : y ∉ support) (tail : TEnvFresh env support) :
    TEnvFresh ((x, y) :: env) support :=
  by
  intro a b hmem hne
  simp only [List.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · cases hmem
    exact ⟨hx, hy⟩
  · exact tail hmem hne

end TEnvFresh

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

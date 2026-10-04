/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.CompactSyntaxFVExplicit
public import LeanPool.NFWeakPartition.CoreFVSimp

/-! Freshness descends through nominal class substitution. -/


public section

namespace NFChoice.ReplaySupport

open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp

theorem not_mem_support_union (v : Var) (left right : Finset Var) (hleft : v ∉ left)
    (hright : v ∉ right) : v ∉ left ∪ right :=
  by
  intro membership
  rcases Finset.mem_union.mp membership with h | h
  · exact hleft h
  · exact hright h

theorem not_mem_class_variable (a b : Var) (h : a ≠ b) : a ∉ (Class.cv b).fv := by
  simpa only [fv_class_cv, Finset.mem_singleton] using h

theorem not_mem_syn_wsbc (v : Var) (A : Class) (x : Var) (ph : Wff) (hA : v ∉ A.fv)
    (hph : v ∉ ph.fv) : v ∉ (synWsbc A x ph).fv :=
  by
  rw [fv_syn_wsbc]
  intro membership
  rcases Finset.mem_union.mp membership with h | h
  · exact hA h
  · exact hph (Finset.mem_erase.mp h).2

end NFChoice.ReplaySupport

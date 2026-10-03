/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.CoreFVSimp
public import LeanPool.NFWeakPartition.CompactSyntaxFVDisable
public import LeanPool.NFWeakPartition.AlphaFocusedSupport

/-! NF weak partition development: FocusedFVPaths. -/


public section

namespace NFChoice.DefinitionLeaves.AlphaFocusedFV

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaTransport
open NFChoice.DefinitionLeaves.AlphaFocusedSupport

/-- The class parameter remains free through `cab outer (wrex inner A p)`. -/
theorem fv_subset_cab_wrex_left {outer inner : Var} {A : Class} {p : Wff}
    (houter : outer ∉ A.fv) (hinner : inner ∉ A.fv) :
    A.fv ⊆ (Class.cab outer (syn_wrex inner A p)).fv :=
  by
  rw [fv_class_cab, fv_syn_wrex]
  apply subset_erase_of_subset_of_not_mem
  · intro u hu
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => hinner (h ▸ hu), hu⟩)
  · exact houter

/-- Complement preserves the preceding focused free-variable embedding. -/
theorem fv_subset_ccompl_cab_wrex_left {outer inner : Var} {A : Class} {p : Wff}
    (houter : outer ∉ A.fv) (hinner : inner ∉ A.fv) :
    A.fv ⊆ (syn_ccompl (Class.cab outer (syn_wrex inner A p))).fv :=
  by
  rw [fv_syn_ccompl]
  exact fv_subset_cab_wrex_left houter hinner


end NFChoice.DefinitionLeaves.AlphaFocusedFV

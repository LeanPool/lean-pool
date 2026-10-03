/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block041

/-! NF weak partition development: NAR4C078C001Part125. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb078_compact_fv_empty_0602 : (nb078_alpha_dummy_765) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0603 (h : Var) :
    (nb078_alpha_dummy_766 h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0604 : (nb078_alpha_dummy_763) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0605 (h : Var) :
    (nb078_alpha_dummy_764 h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0606 : (nb078_alpha_dummy_002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0607 (h : Var) : h ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

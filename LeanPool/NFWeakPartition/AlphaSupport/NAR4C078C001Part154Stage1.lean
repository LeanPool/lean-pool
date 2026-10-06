/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block051

/-! NF weak partition development: NAR4C078C001Part154. -/


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

theorem nb078_compact_fv_empty_0816 : (nb078AlphaDummy1047) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0817 (h : Var) :
    (nb078AlphaDummy1048 h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0818 : (nb078AlphaDummy1045) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0819 (h : Var) :
    (nb078AlphaDummy1046 h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

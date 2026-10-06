/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block027

/-! NF weak partition development: NAR4C078C001Part089. -/


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

theorem nb078_compact_fv_empty_0454 : (nb078AlphaDummy567) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0455 (g : Var) :
    (nb078AlphaDummy568 g) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0456 : (nb078AlphaDummy565) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0457 (g : Var) :
    (nb078AlphaDummy566 g) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

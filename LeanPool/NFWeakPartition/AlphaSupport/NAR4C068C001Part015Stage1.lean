/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block004

/-! NF weak partition development: NAR4C068C001Part015. -/


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

theorem nb068_compact_fv_empty_0058 : (nb068AlphaDummy043) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0059 (f : Var) :
    (nb068AlphaDummy044 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0060 : (nb068AlphaDummy041) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0061 (f : Var) :
    (nb068AlphaDummy042 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0062 : (nb068AlphaDummy000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb068_compact_fv_empty_0063 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part019

/-! NF weak partition development: NAR4H5C095M3Part020. -/


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

theorem nb095_compact_fv_empty_0272 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy340 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0273 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy342 u S_cls) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0274 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy339 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0275 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy341 u S_cls) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0276 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy337 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0277 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy338 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0278 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy335 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0279 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy336 u S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

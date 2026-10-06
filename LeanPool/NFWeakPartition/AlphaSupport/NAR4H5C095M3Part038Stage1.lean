/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part037

/-! NF weak partition development: NAR4H5C095M3Part038. -/


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

theorem nb095_compact_fv_empty_0484 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy620 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0485 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy622 x D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0486 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0487 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0488 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy623 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0489 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy624 x D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0490 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy617 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0491 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy618 x D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0492 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy615 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0493 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy616 x D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

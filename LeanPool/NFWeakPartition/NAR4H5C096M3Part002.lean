/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C096M3Part002Stage3


/-! NF weak partition development: NAR4H5C096M3Part002. -/


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

/-- Checked nominal proof certificate identified upstream as `nb096_focused_refl_0000`. -/
@[expose]
noncomputable def nb096FocusedRefl0000 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TReflOn
      [((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      D.fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0008 D R q dv_D_q)

theorem nb096_compact_fv_empty_0052 (D : Class) (R : Class) :
    (nb096AlphaDummy052 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0053 (R : Class) (q : Var) :
    (nb096AlphaDummy054 R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0054 (D : Class) (R : Class) :
    (nb096AlphaDummy051 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0055 (R : Class) (q : Var) :
    (nb096AlphaDummy053 R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0056 (D : Class) (R : Class) :
    (nb096AlphaDummy049 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0057 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy050 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0058 (D : Class) (R : Class) :
    (nb096AlphaDummy047 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0059 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy048 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0060 (D : Class) (R : Class) :
    (nb096AlphaDummy045 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0061 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy046 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0062 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0063 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0064 (D : Class) (R : Class) :
    (nb096AlphaDummy041 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0065 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy043 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

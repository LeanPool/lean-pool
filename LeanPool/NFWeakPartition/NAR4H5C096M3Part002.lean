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

@[expose]
noncomputable def nb096_focused_refl_0000 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TReflOn
      [((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      D.fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0008 D R q dv_D_q)

theorem nb096_compact_fv_empty_0052 (D : Class) (R : Class) :
    (nb096_alpha_dummy_052 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0053 (R : Class) (q : Var) :
    (nb096_alpha_dummy_054 R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0054 (D : Class) (R : Class) :
    (nb096_alpha_dummy_051 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0055 (R : Class) (q : Var) :
    (nb096_alpha_dummy_053 R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0056 (D : Class) (R : Class) :
    (nb096_alpha_dummy_049 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0057 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_050 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0058 (D : Class) (R : Class) :
    (nb096_alpha_dummy_047 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0059 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_048 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0060 (D : Class) (R : Class) :
    (nb096_alpha_dummy_045 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0061 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_046 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0062 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0063 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0064 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0065 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

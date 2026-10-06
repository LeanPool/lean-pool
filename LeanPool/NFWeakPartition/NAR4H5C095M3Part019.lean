/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part019Stage2


/-! NF weak partition development: NAR4H5C095M3Part019. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_focused_refl_0003`. -/
@[expose]
noncomputable def nb095FocusedRefl0003 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TReflOn
      [((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy293 D R S_cls E), (nb095AlphaDummy294 u S_cls f E)),
        ((nb095AlphaDummy291 D R S_cls E), (nb095AlphaDummy292 u S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      E.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0112 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

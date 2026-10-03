/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part020Stage2


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

@[expose]
noncomputable def nb095_wpp_refl_0116 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TReflOn
      [((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0120 x u D R S_cls f E dv_S_f dv_S_u dv_S_x)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part018Stage3


/-! NF weak partition development: NAR4H5C095M3Part018. -/


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
noncomputable def nb095_wpp_refl_0100 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_R_f : f ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) :
    TReflOn
      [((nb095_alpha_dummy_250 D R S_cls E), (nb095_alpha_dummy_252 x R)),
        ((nb095_alpha_dummy_249 D R S_cls E), (nb095_alpha_dummy_251 x R)),
        ((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0103 x u D R S_cls f E dv_R_f dv_R_u dv_R_x)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

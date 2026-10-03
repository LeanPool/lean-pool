/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C078C001Part134

/-! NF weak partition development: NAR4C078C001Part135. -/


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

theorem nb078_compact_envfresh_0372 (x : Var) (y : Var) (h : Var) :
    TEnvFresh
      [((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
        ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb078_alpha_dummy_765) (nb078_alpha_dummy_766 h)
      (nb078_wpp_notmem_2424) (nb078_wpp_notmem_2425 h)
      (TEnvFresh.consFresh (nb078_alpha_dummy_763) (nb078_alpha_dummy_764 h)
        (nb078_wpp_notmem_2426) (nb078_wpp_notmem_2427 h)
        (TEnvFresh.consFresh (nb078_alpha_dummy_002) h (nb078_wpp_notmem_2428)
          (nb078_wpp_notmem_2429 h)
          (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0512)
            (nb078_wpp_notmem_0513 y)
            (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0514)
              (nb078_wpp_notmem_0515 x) (TEnvFresh.nil ((syn_cid)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

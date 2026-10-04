/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C078C001Part041

/-! NF weak partition development: NAR4C078C001Part042. -/


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

theorem nb078_wpp_notmem_0515 (x : Var) : x ∉ ((synCid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0035 x)

theorem nb078_compact_envfresh_0035 (x : Var) (y : Var) (f : Var) :
    TEnvFresh
      [((nb078AlphaDummy007), (nb078AlphaDummy008 f)),
        ((nb078AlphaDummy005), (nb078AlphaDummy006 f)),
        ((nb078AlphaDummy000), f), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb078AlphaDummy007) (nb078AlphaDummy008 f)
      (nb078_wpp_notmem_0506) (nb078_wpp_notmem_0507 f)
      (TEnvFresh.consFresh (nb078AlphaDummy005) (nb078AlphaDummy006 f)
        (nb078_wpp_notmem_0508) (nb078_wpp_notmem_0509 f)
        (TEnvFresh.consFresh (nb078AlphaDummy000) f (nb078_wpp_notmem_0510)
          (nb078_wpp_notmem_0511 f)
          (TEnvFresh.consFresh (nb078AlphaDummy004) y (nb078_wpp_notmem_0512)
            (nb078_wpp_notmem_0513 y)
            (TEnvFresh.consFresh (nb078AlphaDummy003) x (nb078_wpp_notmem_0514)
              (nb078_wpp_notmem_0515 x) (TEnvFresh.nil ((synCid)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

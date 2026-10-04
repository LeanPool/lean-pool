/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C078C001Part069

/-! NF weak partition development: NAR4C078C001Part070. -/


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

theorem nb078_compact_envfresh_0136 (x : Var) (y : Var) (g : Var) :
    TEnvFresh
      [((nb078AlphaDummy285), (nb078AlphaDummy286 g)),
        ((nb078AlphaDummy283), (nb078AlphaDummy284 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      ((synCid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb078AlphaDummy285) (nb078AlphaDummy286 g)
      (nb078_wpp_notmem_1216) (nb078_wpp_notmem_1217 g)
      (TEnvFresh.consFresh (nb078AlphaDummy283) (nb078AlphaDummy284 g)
        (nb078_wpp_notmem_1218) (nb078_wpp_notmem_1219 g)
        (TEnvFresh.consFresh (nb078AlphaDummy001) g (nb078_wpp_notmem_1220)
          (nb078_wpp_notmem_1221 g)
          (TEnvFresh.consFresh (nb078AlphaDummy004) y (nb078_wpp_notmem_0512)
            (nb078_wpp_notmem_0513 y)
            (TEnvFresh.consFresh (nb078AlphaDummy003) x (nb078_wpp_notmem_0514)
              (nb078_wpp_notmem_0515 x) (TEnvFresh.nil ((synCid)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

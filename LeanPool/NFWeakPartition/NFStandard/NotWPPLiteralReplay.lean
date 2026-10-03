/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.WPP
public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk018Compact001Block001
public import LeanPool.NFWeakPartition.ReplaySupport.ClosedProofSoundness

/-! NF weak partition development: NFStandard.NotWPPLiteralReplay. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal.BoundedNominalLoweringBridgeDev004

/- Soundness of the accepted nominal replay, stated at its source WPP. -/

theorem literalHailperin_valid_not_WPP {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) : Wff.Valid S (.neg syn_wwpp) :=
  NFChoice.ReplaySupport.valid_closed_of_nominal_proof (.neg syn_wwpp)
    (by simp only [Wff.neg, Wff.fv, fv_syn_wwpp, Finset.union_empty])
    NFChoice.DirectNominalPrf.WPPReplay.g_wppfiniteblocknotwppndv hH

/-- The accepted replay proves the exact lowered WPP sentence from the literal basis. -/
theorem literalHailperin_proves_not_WPP : LiteralHailperinNF ⊢ₛ' Fol.bd_not WPP :=
  by
  unfold WPP
  exact
    NFChoice.ReplaySupport.derives_not_of_nominal_validity syn_wwpp WPPSyntax fv_syn_wwpp
      lowerClosed_syn_wwpp (fun _ _ hH => literalHailperin_valid_not_WPP hH)

end NFChoice.Foundation.NFStandard

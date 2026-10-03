/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.LoweringTotality
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart003

/-! NF weak partition development: NFStandard.WPP. -/


public section

namespace NFChoice.Foundation.NFStandard

open NFChoice.SemanticCore.PartialLowering
open NFChoice.Compiler.CompactSourceSyntax

/-- The closed intrinsic formula obtained by lowering the accepted WPP source. -/
@[expose]
def WPPSyntax : Sentence :=
  (lowerClosed syn_wwpp).getD .falsum

/- The accepted nominal WPP source lowers successfully to `WPPSyntax`. -/

theorem lowerClosed_syn_wwpp : lowerClosed syn_wwpp = some WPPSyntax :=
  option_eq_some_getD (lowerClosed syn_wwpp) .falsum
    (lowerClosed_exists syn_wwpp NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp)

/-- WPP as a Flypitch sentence, exactly lowered from the accepted source. -/
@[expose]
def WPP : Fol.sentence LNF :=
  Formula.toFlypitch WPPSyntax


end NFChoice.Foundation.NFStandard

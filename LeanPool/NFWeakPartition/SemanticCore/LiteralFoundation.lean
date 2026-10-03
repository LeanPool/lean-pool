/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.Basic
public import LeanPool.NFWeakPartition.ExactLiteralTrial.NFChoiceExactLiteral

/-! NF weak partition development: SemanticCore.LiteralFoundation. -/


public section

namespace NFChoice.SemanticCore

open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial

/-! This module fixes the replay boundary to the append-only literal Hailperin
theory.  Its pair/singleton class terms are unary predicates expanded
extensionally; no representative set for a nested class term is postulated.
-/


/-- The literal trial's ax-ext sentence realizes exactly structure extensionality. -/
theorem extensional_iff_literal_axExt (S : Fol.Structure LNF) :
    Extensional S ↔ Fol.realize_sentence S (literalAxiomFormula .axExt) := by
  simpa [literalAxiomFormula, literalAxiomSyntax, literalAxExt, axiomFormula, axiomSyntax,
    axExt] using extensional_iff_foundation_axExt S

/-- The exact source target consumed by the generated semantic replay. -/
abbrev LiteralReplayTarget (sourceChoiceNF : Fol.sentence LNF) : Prop :=
  LiteralSourceNFProvesNotChoiceTarget sourceChoiceNF


end NFChoice.SemanticCore

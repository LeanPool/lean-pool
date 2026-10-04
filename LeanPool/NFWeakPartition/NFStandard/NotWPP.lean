/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.Equivalence
public import LeanPool.NFWeakPartition.NFStandard.NotWPPLiteralReplay

/-! NF weak partition development: NFStandard.NotWPP. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial

/-- The repository's finite presentation proves the negation of WPP. -/
theorem hailperin_proves_not_WPP : HailperinNF ⊢ₛ' Fol.bdNot WPP :=
  hailperinPresentation_deductivelyEquivalent.mpr literalHailperin_proves_not_WPP

/-- Standard NF proves the negation of WPP, by full finite-basis equivalence. -/
theorem NF_proves_not_WPP : NF ⊢ₛ' Fol.bdNot WPP :=
  nf_hailperin_deductivelyEquivalent.mpr hailperin_proves_not_WPP


end NFChoice.Foundation.NFStandard

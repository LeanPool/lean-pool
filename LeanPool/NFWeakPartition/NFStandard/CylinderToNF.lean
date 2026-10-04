/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.CylinderCompiler

/-! NF weak partition development: NFStandard.CylinderToNF. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering
open NFChoice.Foundation.ExactLiteralTrial

/-! This module is the presentation-independent end of the Hailperin compiler.
Once a structure supplies the small `CylinderAlgebra` interface, the generic
compiler constructs the extension of every stratified formula.  The lemmas
below turn those constructed extensions back into the closed first-order
sentences comprising `NF`.
-/


/-- A cylinder algebra realizes each closed stratified-comprehension axiom. -/
theorem realize_comprehensionInstance_of_cylinder {S : Fol.Structure LNF}
    (C : CylinderAlgebra S) {n : Nat} (p : Formula (n + 1)) (hp : Formula.Stratified p) :
    Fol.realizeSentence S (comprehensionInstance p) :=
  by
  apply (Fol.realize_sentence_bd_alls).2
  intro xs
  apply (formulaHolds_toFlypitch xs (comprehensionBody p)).1
  apply (formulaHolds_ex).2
  refine ⟨C.comprehensionSet p hp xs, ?_⟩
  apply (formulaHolds_eqCandidateToPredicate xs (C.comprehensionSet p hp xs) p).2
  exact C.mem_comprehensionSet p hp xs

/-- Extensionality plus a cylinder algebra is a model of standard `NF`.
No feature of the particular Metamath Hailperin-derived finite presentation is used here.
-/
theorem models_NF_of_cylinder {S : Fol.Structure LNF} (C : CylinderAlgebra S)
    (hExt : Fol.realizeSentence S (literalAxiomFormula .axExt)) :
    Fol.allRealizeSentence S NF := by
  intro f hf
  rcases hf with hEq | hComp
  · simpa [hEq] using hExt
  · rcases hComp with ⟨n, p, hp, rfl⟩
    exact realize_comprehensionInstance_of_cylinder C p hp


end NFChoice.Foundation.NFStandard

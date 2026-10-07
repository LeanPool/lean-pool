/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.CylinderToNF
public import LeanPool.NFWeakPartition.NFStandard.HailperinAlgebra
public import LeanPool.NFWeakPartition.NFStandard.HailperinPresentationBridge
public import LeanPool.NFWeakPartition.NFStandard.ToHailperin

/-! NF weak partition development: NFStandard.Equivalence. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial

/-! The two directions are deliberately exposed at the model boundary.  The
forward direction verifies the eleven axioms of Metamath's Hailperin-derived presentation by
ordinary
stratified comprehension.  The reverse direction instantiates the uniform
cylinder compiler with the operations constructed from those eleven axioms.
First-order completeness then converts equality of model classes into full
deductive equivalence.
-/


/-- The exact literal Hailperin basis supplies every stratified comprehension. -/
theorem literalHailperin_models_NF {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S LiteralHailperinNF) :
    Fol.allRealizeSentence S NF :=
  models_NF_of_cylinder (hailperinCylinderAlgebra hH) (hH (literalAxiom_mem .axExt))

/-- Standard NF and the exact literal finite basis have the same models. -/
theorem models_NF_iff_literalHailperinNF (S : Fol.Structure LNF) :
    Fol.allRealizeSentence S NF ↔ Fol.allRealizeSentence S LiteralHailperinNF :=
  ⟨nf_models_literalHailperin, literalHailperin_models_NF⟩

/-- Standard NF and the exact literal finite basis have the same consequences. -/
theorem nf_literalHailperin_deductivelyEquivalent :
    DeductivelyEquivalent NF LiteralHailperinNF :=
  deductivelyEquivalent_of_models_iff models_NF_iff_literalHailperinNF

/-- The existing finite theory `HailperinNF` supplies standard NF. -/
theorem hailperin_models_NF {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) : Fol.allRealizeSentence S NF :=
  literalHailperin_models_NF (foundationModel_to_literalModel hH)

/-- Standard NF supplies the existing finite theory `HailperinNF`. -/
theorem nf_models_HailperinNF {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S NF) : Fol.allRealizeSentence S HailperinNF :=
  literalModel_to_foundationModel (nf_models_literalHailperin hNF)

/-- Standard `NF` and finite `HailperinNF` have exactly the same models. -/
theorem models_NF_iff_HailperinNF (S : Fol.Structure LNF) :
    Fol.allRealizeSentence S NF ↔ Fol.allRealizeSentence S HailperinNF :=
  ⟨nf_models_HailperinNF, hailperin_models_NF⟩

/-- Full equivalence of the standard stratified-comprehension theory and
Metamath's Hailperin-derived finite first-order presentation.
-/
theorem nf_hailperin_deductivelyEquivalent : DeductivelyEquivalent NF HailperinNF :=
  deductivelyEquivalent_of_models_iff models_NF_iff_HailperinNF


end NFChoice.Foundation.NFStandard

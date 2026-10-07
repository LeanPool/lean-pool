/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.Basic

/-! NF weak partition development: NFStandard.TheoryEquivalence. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol

/-! Small semantic-to-syntactic utilities used to state the equivalence between
standard `NF` and the finite theory `HailperinNF`.  Keeping this layer generic
makes clear that the substantive work is exactly the equivalence of their
models; Gödel completeness then converts that equivalence into equality of
all first-order consequences.
-/


/-- Two sentence theories have exactly the same first-order consequences. -/
@[expose]
def DeductivelyEquivalent (T U : Fol.SentTheory LNF) : Prop :=
  ∀ f : Fol.sentence LNF, (T ⊢ₛ' f) ↔ (U ⊢ₛ' f)

/-- Semantic inclusion of model classes transfers every formal consequence. -/
theorem consequence_of_model_inclusion {T U : Fol.SentTheory LNF} {f : Fol.sentence LNF}
    (hmodels : ∀ (S : Fol.Structure LNF),
        Fol.allRealizeSentence S U → Fol.allRealizeSentence S T)
    (hf : T ⊢ₛ' f) : U ⊢ₛ' f :=
  by
  apply (Fol.completeness U f).2
  intro S hS hU
  exact (Fol.completeness T f).1 hf hS (hmodels S hU)

/-- Theories with the same models have exactly the same formal consequences. -/
theorem deductivelyEquivalent_of_models_iff {T U : Fol.SentTheory LNF}
    (hmodels : ∀ (S : Fol.Structure LNF),
        Fol.allRealizeSentence S T ↔ Fol.allRealizeSentence S U) :
    DeductivelyEquivalent T U := by
  intro f
  constructor
  · exact consequence_of_model_inclusion (fun S hU => (hmodels S).2 hU)
  · exact consequence_of_model_inclusion (fun S hT => (hmodels S).1 hT)

/-- A theorem can be transported across deductively equivalent theories. -/
theorem DeductivelyEquivalent.mp {T U : Fol.SentTheory LNF}
    (h : DeductivelyEquivalent T U) {f : Fol.sentence LNF} (hf : T ⊢ₛ' f) : U ⊢ₛ' f :=
  (h f).1 hf

/-- The reverse transport across deductively equivalent theories. -/
theorem DeductivelyEquivalent.mpr {T U : Fol.SentTheory LNF}
    (h : DeductivelyEquivalent T U) {f : Fol.sentence LNF} (hf : U ⊢ₛ' f) : T ⊢ₛ' f :=
  (h f).2 hf


end NFChoice.Foundation.NFStandard

/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.TheoryEnumerability
public import LeanPool.PointwiseComposition.FailureOfComposition.KleeneNormalForm

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
From a partial-recursive axiom enumerator in Mathlib's fixed program numbering
to enumerability of theorem codes. The enumerator may diverge on inputs; its
range, rather than totality, specifies the axioms.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition

/-- The range of a numbered partial-recursive program is enumerable. -/
theorem partial_program_range_re (a : ℕ) : REPred (fun n : ℕ => ∃ x : ℕ, n ∈ Kleene.eval a x) :=
  by
  have hT : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => Kleene.T₁ a p.2.1 p.2.2) :=
    Kleene.T₁_primrec.comp
      (((Primrec.const a).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))
  have hU : PrimrecPred (fun p : ℕ × (ℕ × ℕ) => Kleene.U p.2.2 = p.1) :=
    Primrec.eq.comp (Kleene.U_primrec.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst
  have hr :=
    (PointwiseComposition.REPred.projection
      ((PointwiseComposition.REPred.and hT.computablePred.to_re) hU.computablePred.to_re))
  apply REPred.of_eq hr
  intro n
  change (∃ p : ℕ × ℕ, Kleene.T₁ a p.1 p.2 ∧ Kleene.U p.2 = n) ↔ _
  simp only [Prod.exists]
  exact exists_congr fun x => (Kleene.normal_form a x n).symm

/-- The manuscript's partial recursive axiom enumeration makes AxiomCodes r.e. -/
theorem axiom_codes_re_of_program_enumerator (T : ArithmeticTheory) (a : ℕ)
    (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) : REPred (AxiomCodes T) :=
  (partial_program_range_re a).of_eq (fun n => (ha n).symm)

/-- An axiom enumerator suffices to enumerate the deductive closure. -/
theorem theorem_codes_re_of_program_enumerator (T : ArithmeticTheory) (a : ℕ)
    (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) : REPred (TheoremCodes T) :=
  theorem_codes_re_of_axiom_codes T (axiom_codes_re_of_program_enumerator T a ha)

end FailureOfComposition

end

end PointwiseComposition

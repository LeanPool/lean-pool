/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteWitnessGraphs
public import LeanPool.PointwiseComposition.FailureOfComposition.MinimizationPersistence

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
A concrete nowhere-defined program in the accepted Mathlib numbering.
The program searches for a zero of successor; its index is 11.
Its graph is proved empty inside every model of PA, including nonstandard models.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.Evaluator

open CategoricalRiceShapiro.ArithmeticCode

open FailureOfComposition.ConcreteWitnessGraphs

namespace FailureOfComposition
namespace ConcreteEmptyGraph

/-- Search for a zero of successor, starting from the supplied search position. -/
def concreteEmptyIndex : ℕ :=
  Encodable.encode (Nat.Partrec.Code.rfind' Nat.Partrec.Code.succ)

@[simp]
theorem concreteEmptyIndex_eq : concreteEmptyIndex = 11 :=
  rfl

/-- Absence of successful computations at a stage, expressed in PA's language. -/
def noComputationFormula (q : ℕ) : ArithmeticSemisentence 1 :=
  “s. ∀ u, ∀ y, ¬!certificateSentence s↑q u y”

variable {M : Type*} [ORingStructure M]

private theorem noComputationFormula_eval [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (s : M) :
    Semiformula.Evalb ![s] (noComputationFormula q) ↔
      ∀ u y : M,
        ¬Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  simp [noComputationFormula, certificateSentence, Semiformula.eval_substs, numeral_eq_natCast]

/-- No stage, input, or output in a PA model is a successful computation of
`rfind' succ`; the induction is PA induction on the model's stage parameter. -/
theorem concreteEmpty_no_computation [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] :
    ∀ s u y : M,
      ¬Semiformula.Evalb ![s, (concreteEmptyIndex : M), u, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  have := models_inductionScheme_univ (M := M)
  have : Inhabited M := ⟨0⟩
  have hzero :
    ∀ u y : M,
      ¬Semiformula.Evalb ![(0 : M), (concreteEmptyIndex : M), u, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) :=
    by
    intro u y h
    have hhist := (evalnCertificateFormula_eval_history_iff 0 (concreteEmptyIndex : M) u y).mp h
    have hlt :=
      ((eval_codeHistoryEvaluator_succ_iff_cell 0 (concreteEmptyIndex : M) u y).mp hhist).1
    exact (not_lt_of_ge (FFL.FirstOrder.Arithmetic.zero_le u)) hlt
  have hstep (s : M)
    (ih :
      ∀ u y : M,
        ¬Semiformula.Evalb ![s, (concreteEmptyIndex : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    ∀ u y : M,
      ¬Semiformula.Evalb ![s + 1, (concreteEmptyIndex : M), u, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) :=
    by
    intro u y h
    have hs : (0 : M) < s + 1 :=
      lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le s) (lt_add_one s)
    obtain ⟨_, x, hx, hcase⟩ :=
      (evalnCertificateFormula_tag_seven_iff concreteEmptyIndex (by decide) (s + 1) u y hs).mp h
    have hsub : partrecCodePayload concreteEmptyIndex = 1 := by decide
    rw [hsub] at hx
    have hx' : u < s + 1 ∧ x = u + 1 := by
      simpa [baseOutput] using (base_computation_iff 1 (by decide) (s + 1) u x).mp hx
    rcases hcase with ⟨_, hr⟩ | ⟨hx0, _⟩
    · apply ih _ y
      simpa only [add_sub_self] using hr
    · have hp : (0 : M) < u + 1 :=
        lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le u) (lt_add_one u)
      exact (ne_of_gt hp) (hx'.2.symm.trans hx0)
  intro s
  refine
    InductionScheme.succ_induction (C := Set.univ) (P := fun s : M =>
      ∀ u y : M,
        ¬Semiformula.Evalb ![s, (concreteEmptyIndex : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4))
      ⟨fun _ => default, Rew.emb ▹ noComputationFormula concreteEmptyIndex, trivial, ?_⟩ hzero
      hstep s
  intro x
  rw [← noComputationFormula_eval concreteEmptyIndex x]
  simp [Semiformula.eval_emb]

/-- The unbounded computation graph of the concrete empty program is empty. -/
theorem concreteEmpty_unbounded_computation_iff [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (u y : M) :
    (∃ s : M,
        Semiformula.Evalb ![s, (concreteEmptyIndex : M), u, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4)) ↔
      False :=
  by
  constructor
  · rintro ⟨s, h⟩
    exact concreteEmpty_no_computation s u y h
  · exact False.elim

end ConcreteEmptyGraph
end FailureOfComposition

end

end PointwiseComposition

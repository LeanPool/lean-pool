/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Certificate

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The conditional induction principle for certificate persistence

For a standard index `q`, write `C(s, q, u, y)` for the raw evaluator certificate
`evalnCertificateFormula` at `![s, q, u, y]`, and `P_q(s)` for
`∀ t u y, s ≤ t → C(s, q, u, y) → C(t, q, u, y)`.

`persistenceFormula q` is an explicit arithmetic formula in one variable, and
`persistenceFormula_eval_iff` proves that it defines `P_q` in every model of
`𝐈𝐎𝐩𝐞𝐧`.  `models_inductionScheme_univ` proves that a model of `𝐏𝐀` satisfies
the full induction scheme that `𝐏𝐀` contains.
`certificate_persistence_of_stage_induction` applies successor induction from
that scheme to `persistenceFormula q`: from `P_q(0)` and
`∀ s, P_q(s) → P_q(s + 1)` it derives `P_q(s)` for every `s`.

The successor premise is a hypothesis of that theorem.  The stage-zero premise
is proved here, by `evalnCertificateFormula_natCode_persist_of_stage_zero`, for
every standard index and independently of its constructor number: at stage `0`
no evaluator history has a row, so the source certificate is refutable and the
implication holds vacuously.

The file proves no conditional persistence case at a constructor number.  The
constructor-`6` cases and the full tag-6 theorem are in
`Evaluator.PrimitiveRecursionPersistence`; persistence for every standard index,
which needs the external induction on the index, is not proved anywhere in the
library.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

namespace CategoricalRiceShapiro
namespace Evaluator

variable {M : Type*} [ORingStructure M]

/-- The certificate formula as a plain four-place arithmetic semisentence. -/
def certificateSentence : ArithmeticSemisentence 4 :=
  (evalnCertificateFormula : ArithmeticSemisentence 4)

/-- The persistence predicate at the standard index `q`, as an arithmetic
formula in the source stage:
`∀ t u y, s ≤ t → C(s, q, u, y) → C(t, q, u, y)`. -/
def persistenceFormula (q : ℕ) : ArithmeticSemisentence 1 :=
  “s. ∀ t, ∀ u, ∀ y, s ≤ t → !certificateSentence s↑q u y → !certificateSentence t↑q u y”

/-- The persistence formula defines the actual persistence predicate. -/
theorem persistenceFormula_eval_iff [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ) (s : M) :
    Semiformula.Evalb ![s] (persistenceFormula q) ↔
      ∀ t u y : M,
        s ≤ t →
          Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4) →
            Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by simp [persistenceFormula, certificateSentence, Semiformula.eval_substs, numeral_eq_natCast]

/-- The full induction scheme of `𝐏𝐀` holds in every model of `𝐏𝐀`. -/
theorem models_inductionScheme_univ [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
  by
  have : InductionScheme ℒₒᵣ Set.univ ≼ 𝐏𝐀 :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  exact models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)

/-- **Conditional internal induction for certificate persistence** at a fixed
standard index `q`.  The base and successor premises are explicit; this is not
a proof of persistence.  The induction is the successor induction of `𝐏𝐀`
applied to `persistenceFormula q`. -/
theorem certificate_persistence_of_stage_induction [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (q : ℕ)
    (hzero :
      ∀ t u y : M,
        (0 : M) ≤ t →
          Semiformula.Evalb ![(0 : M), ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4) →
            Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4))
    (hsucc :
      ∀ s : M,
        (∀ t u y : M,
            s ≤ t →
              Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4) →
                Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4)) →
          ∀ t u y : M,
            s + 1 ≤ t →
              Semiformula.Evalb ![s + 1, ((q : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4) →
                Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    ∀ s t u y : M,
      s ≤ t →
        Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) →
          Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  have := models_inductionScheme_univ (M := M)
  have : Inhabited M := ⟨0⟩
  intro s
  refine
    InductionScheme.succ_induction (C := Set.univ) (P := fun s : M =>
      ∀ t u y : M,
        s ≤ t →
          Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4) →
            Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
              (evalnCertificateFormula : ArithmeticSemisentence 4))
      ⟨fun _ => default, Rew.emb ▹ persistenceFormula q, trivial, ?_⟩ hzero hsucc s
  intro x
  rw [← persistenceFormula_eval_iff q x]
  simp [Semiformula.eval_emb]

/-!
### The stage-zero premise

At stage `0` no evaluator history has a row, so no certificate holds there and
the premise is vacuous.  Its conclusion is the `hzero` hypothesis of
`certificate_persistence_of_stage_induction` verbatim.

The theory assumptions are `𝐏𝐀` and `𝐏𝐀⁻`.  The second is an elaboration
requirement of the statement, since the standard-index cast `((q : ℕ) : M)`
needs it; it is no additional strength, `𝐏𝐀` proving every axiom of `𝐏𝐀⁻`.
Wherever `𝐈𝐎𝐩𝐞𝐧` is in scope the instance is synthesized and the argument is
invisible. -/

/-- **Stage-zero persistence.**  For a standard index `q`, a certificate at
stage `0` persists to every stage `t`, vacuously: at stage `0` the certificate
is refutable.  The proof uses no persistence theorem, no induction, no
constructor-number hypothesis and no smaller-index hypothesis, so the theorem
holds at every standard index. -/
theorem evalnCertificateFormula_natCode_persist_of_stage_zero [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻]
    (q : ℕ) :
    ∀ t u y : M,
      (0 : M) ≤ t →
        Semiformula.Evalb ![(0 : M), ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) →
          Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by
  intro t u y _ source_certificate
  have source_history :=
    (evalnCertificateFormula_eval_history_iff (0 : M) ((q : ℕ) : M) u y).mp source_certificate
  obtain ⟨hlt, -⟩ :=
    (eval_codeHistoryEvaluator_succ_iff_cell (0 : M) ((q : ℕ) : M) u y).mp source_history
  exact absurd hlt (not_lt_of_ge (FFL.FirstOrder.Arithmetic.zero_le u))

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition

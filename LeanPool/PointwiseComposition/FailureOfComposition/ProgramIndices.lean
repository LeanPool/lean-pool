/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GodelGraph
public import LeanPool.PointwiseComposition.FailureOfComposition.ProductiveGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Index-level consequence of the arithmetization assumptions explicitly stated
in v36, equations (composition-graph) and (graph-realization).

`Arithmetization` is a hypothesis, not a constructed instance for Mathlib's
evaluator. In particular, the realization field is not discharged here.
No theorem in this file identifies standard-model equivalence with PA provability.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace ProgramIndices

open ProofSearch

noncomputable section

/-- The paper's definedness equivalence and common-value clause. -/
def kleeneEqAt (F G : Graph) (n : ℕ) : ArithmeticSentence :=
  “((∃ y, !F.val !!(n)y) ↔ (∃ y, !G.val !!(n)y)) ∧
      ((∃ y, !F.val !!(n)y) → ∃ y, !F.val !!(n)y ∧ !G.val !!(n)y)”

/-- Functionality is what makes output-quantified graph equality the same
as the manuscript's equality, including agreement on divergence. -/
theorem kleeneEqAt_iff_eqAt (F G : Graph) (hF : Functional F) (hG : Functional G) (n : ℕ) :
    𝐏𝐀 ⊢ kleeneEqAt F G n ⇔ₗ eqAt F G n :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hf : V↓[ℒₒᵣ] ⊧ functionalSentence F :=
    consequence_iff.mp (Theory.Proof.sound hF) V inferInstance
  have hg : V↓[ℒₒᵣ] ⊧ functionalSentence G :=
    consequence_iff.mp (Theory.Proof.sound hG) V inferInstance
  simp only [models_iff, functionalSentence_eval] at hf hg
  simp only [kleeneEqAt, Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue, eqAt,
    Semantics.models_iff, Semantics.And.models_and, models_iff, Semiformula.eval_ex,
    Nat.succ_eq_add_one, Semiformula.eval_substs, Matrix.comp₂, Semiterm.val_operator,
    Matrix.comp₀, Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast, Semiterm.val_bvar,
    Matrix.cons_val_fin_one, Semantics.Imp.models_imply, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, forall_exists_index, Semiformula.eval_all,
    LogicalConnective.HomClass.map_iff, LogicalConnective.Prop.iff_eq]
  constructor
  · rintro ⟨hdom, hcommon⟩ y
    constructor
    · intro hy
      obtain ⟨z, hzF, hzG⟩ := hcommon y hy
      have heq := hf (n : V) y z hy hzF
      simpa [heq] using hzG
    · intro hy
      obtain ⟨w, hw⟩ := hdom.mpr ⟨y, hy⟩
      obtain ⟨z, hzF, hzG⟩ := hcommon w hw
      have heq := hg (n : V) y z hy hzG
      simpa [heq] using hzF
  · intro h
    refine ⟨exists_congr h, ?_⟩
    intro y hy
    exact ⟨y, hy, (h y).mp hy⟩

/-- The two PA-level arithmetization theorems assumed in v36, together with
functionality. Supplying this structure is a substantial separate obligation. -/
structure Arithmetization where
  /-- The evaluation construction in `FailureOfComposition.ProgramIndices.Arithmetization`. -/
  evaluation : ℕ → ℕ → Part ℕ
  /-- The graph construction in `FailureOfComposition.ProgramIndices.Arithmetization`. -/
  graph : ℕ → Graph
  /-- The comp Index construction in `FailureOfComposition.ProgramIndices.Arithmetization`. -/
  compIndex : ℕ → ℕ → ℕ
  compIndex_primrec : Primrec₂ compIndex
  adequate : ∀ e x y, (graph e).val.Evalb ![x, y] ↔ y ∈ evaluation e x
  functional : ∀ e, Functional (graph e)
  composition : ∀ e d, Uniform 𝐏𝐀 (graph (compIndex e d)) (comp (graph e) (graph d))
  realization : ∀ F : Graph, Functional F → ∃ e, Uniform 𝐏𝐀 (graph e) F

theorem uniform_to_pointwise (T : ArithmeticTheory) [𝐏𝐀 ≼ T] {F G : Graph}
    (h : Uniform 𝐏𝐀 F G) : Pointwise T F G :=
  by
  intro n
  apply WeakerThan.pbl (𝓢 := 𝐏𝐀)
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hu : V↓[ℒₒᵣ] ⊧ uniformSentence F G :=
    consequence_iff.mp (Theory.Proof.sound h) V inferInstance
  simp only [models_iff, uniformSentence_eval] at hu
  simpa only [models_iff, eqAt_eval] using hu (n : V)

theorem uniform_comp {F F' G G' : Graph} (hF : Uniform 𝐏𝐀 F F') (hG : Uniform 𝐏𝐀 G G') :
    Uniform 𝐏𝐀 (comp F G) (comp F' G') :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have hf : V↓[ℒₒᵣ] ⊧ uniformSentence F F' :=
    consequence_iff.mp (Theory.Proof.sound hF) V inferInstance
  have hg : V↓[ℒₒᵣ] ⊧ uniformSentence G G' :=
    consequence_iff.mp (Theory.Proof.sound hG) V inferInstance
  simp only [models_iff, uniformSentence_eval] at hf hg ⊢
  intro x z
  simp only [comp_eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact exists_congr fun y => and_congr (hg x y) (hf y z)

/-- The Pointwise Index construction in `FailureOfComposition.ProgramIndices`. -/
def PointwiseIndex (A : Arithmetization) (T : ArithmeticTheory) (e d : ℕ) : Prop :=
  ∀ n, T ⊢ kleeneEqAt (A.graph e) (A.graph d) n

theorem pointwiseIndex_iff (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (e d : ℕ) :
    PointwiseIndex A T e d ↔ Pointwise T (A.graph e) (A.graph d) :=
  by
  have h (n : ℕ) : T ⊢ kleeneEqAt (A.graph e) (A.graph d) n ⇔ₗ eqAt (A.graph e) (A.graph d) n :=
    WeakerThan.pbl (kleeneEqAt_iff_eqAt _ _ (A.functional e) (A.functional d) n)
  constructor
  · intro he n
    have hn := he n
    cl_prover[h n, hn]
  · intro he n
    have hn := he n
    cl_prover[h n, hn]

/-- The index Setoid construction in `FailureOfComposition.ProgramIndices`. -/
def indexSetoid (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Setoid ℕ
    where
  r := PointwiseIndex A T
  iseqv :=
    { refl := fun e => (pointwiseIndex_iff A T e e).mpr ((pointwise_equivalence T).refl _)
      symm := fun {e d} h =>
        (pointwiseIndex_iff A T d e).mpr
          ((pointwise_equivalence T).symm ((pointwiseIndex_iff A T e d).mp h))
      trans := fun {e d f} h₁ h₂ =>
        (pointwiseIndex_iff A T e f).mpr
          ((pointwise_equivalence T).trans ((pointwiseIndex_iff A T e d).mp h₁)
            ((pointwiseIndex_iff A T d f).mp h₂)) }

/-- The No Index Quotient Composition construction in `FailureOfComposition.ProgramIndices`. -/
def NoIndexQuotientComposition (A : Arithmetization) (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Prop :=
  ¬∃ C : Quotient (indexSetoid A T) → Quotient (indexSetoid A T) → Quotient (indexSetoid A T),
      ∀ e d,
        C (Quotient.mk (indexSetoid A T) e) (Quotient.mk (indexSetoid A T) d) =
          Quotient.mk (indexSetoid A T) (A.compIndex e d)

theorem index_noncongruence_of_graph_noncongruence (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T]
    (h :
      ∃ F I G : Graph,
        Functional F ∧
          Functional I ∧ Functional G ∧ Pointwise T F I ∧ ¬Pointwise T (comp F G) (comp I G)) :
    ∃ f i g : ℕ,
      PointwiseIndex A T f i ∧ ¬PointwiseIndex A T (A.compIndex f g) (A.compIndex i g) :=
  by
  obtain ⟨F, I, G, hF, hI, hG, hFI, hn⟩ := h
  obtain ⟨f, hf⟩ := A.realization F hF
  obtain ⟨i, hi⟩ := A.realization I hI
  obtain ⟨g, hg⟩ := A.realization G hG
  have eqv := pointwise_equivalence T
  have hfg : Pointwise T (A.graph (A.compIndex f g)) (comp F G) :=
    eqv.trans (uniform_to_pointwise T (A.composition f g))
      (uniform_to_pointwise T (uniform_comp hf hg))
  have hig : Pointwise T (A.graph (A.compIndex i g)) (comp I G) :=
    eqv.trans (uniform_to_pointwise T (A.composition i g))
      (uniform_to_pointwise T (uniform_comp hi hg))
  refine
    ⟨f, i, g,
      (pointwiseIndex_iff A T f i).mpr
        (eqv.trans (uniform_to_pointwise T hf)
          (eqv.trans hFI (eqv.symm (uniform_to_pointwise T hi)))),
      ?_⟩
  intro hc
  exact hn (eqv.trans (eqv.symm hfg) (eqv.trans ((pointwiseIndex_iff A T _ _).mp hc) hig))

theorem no_index_quotient_of_graph_noncongruence (A : Arithmetization) (T : ArithmeticTheory)
    [𝐏𝐀 ≼ T]
    (h :
      ∃ F I G : Graph,
        Functional F ∧
          Functional I ∧ Functional G ∧ Pointwise T F I ∧ ¬Pointwise T (comp F G) (comp I G)) :
    NoIndexQuotientComposition A T :=
  by
  obtain ⟨f, i, g, hfi, hcomp⟩ := index_noncongruence_of_graph_noncongruence A T h
  exact no_quotient_composition_of_noncongruence (indexSetoid A T) A.compIndex f i g hfi hcomp

theorem no_index_quotient_via_godel (A : Arithmetization) (T : ArithmeticTheory) [T.Δ₁]
    [Consistent T] [𝐏𝐀 ≼ T] : NoIndexQuotientComposition A T :=
  no_index_quotient_of_graph_noncongruence A T (graph_noncongruence_via_godel T)

/-- Independent productiveness route, with r.e. theorem codes explicit. -/
theorem no_index_quotient_via_productiveness (A : Arithmetization) (T : ArithmeticTheory)
    [Consistent T] [𝐏𝐀 ≼ T] (hT : REPred (TheoremCodes T)) : NoIndexQuotientComposition A T :=
  no_index_quotient_of_graph_noncongruence A T
    (graph_noncongruence_of_unprovable_divergence T
      (exists_true_unprovable_divergence_of_theorem_codes T hT))

end

end ProgramIndices
end FailureOfComposition

end

end PointwiseComposition

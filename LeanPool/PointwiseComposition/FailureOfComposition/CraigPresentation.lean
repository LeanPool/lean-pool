/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.TheoryEnumerability
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.Definability

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
A decidable presentation of an r.e. arithmetic theory.
Each axiom is padded by a tautology carrying a PA derivation that its original
code belongs to the represented axiom set. The derivation checker and syntax
operations are provably Delta-one over IΣ1. -/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open FFL.FirstOrder.Arithmetic.Bootstrapping

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FailureOfComposition
namespace CraigPresentation

noncomputable section

/-- The axiom Formula construction in `FailureOfComposition.CraigPresentation`. -/
def axiomFormula (T : ArithmeticTheory) : ArithmeticSemisentence 1 :=
  codeOfREPred (AxiomCodes T)

/-- The padded construction in `FailureOfComposition.CraigPresentation`. -/
def padded (σ : ArithmeticSentence) (d : ℕ) : ArithmeticSentence :=
  σ ⋏ ((“!!(d) = !!(d)”) ⋎ (“!!(d) ≠ !!(d)”))

/-- The pad Graph construction in `FailureOfComposition.CraigPresentation`. -/
def padGraph : Σ₁.Semisentence 3 :=
  .mkSigma
    (“f s d.
      ∃ nd e ne t,
        !Bootstrapping.ObjectArithmetic.numeralGraph nd d ∧
          !qqEQDef e nd nd ∧ !qqNEQDef ne nd nd ∧ !qqOrDef t e ne ∧ !qqAndDef f s t”)

/-- The check Sigma construction in `FailureOfComposition.CraigPresentation`. -/
def checkSigma (T : ArithmeticTheory) : Σ₁.Semisentence 2 :=
  .mkSigma
    (“s d.
      ∃ ns a,
        !Bootstrapping.ObjectArithmetic.numeralGraph ns s ∧
          !(substs1Graph ℒₒᵣ)a ns !!(⌜axiomFormula T⌝) ∧ !(proof 𝐏𝐀).sigma d a”)

/-- The check Pi construction in `FailureOfComposition.CraigPresentation`. -/
def checkPi (T : ArithmeticTheory) : Π₁.Semisentence 2 :=
  .mkPi
    (“s d.
      ∀ ns a,
        !Bootstrapping.ObjectArithmetic.numeralGraph ns s →
          !(substs1Graph ℒₒᵣ)a ns !!(⌜axiomFormula T⌝) → !(proof 𝐏𝐀).pi d a”)

/-- The characteristic construction in `FailureOfComposition.CraigPresentation`. -/
def characteristic (T : ArithmeticTheory) : ∆₁.Semisentence 1 :=
  .mkDelta (.mkSigma (“f. ∃ s < f, ∃ d < f, !padGraph f s d ∧ !(checkSigma T)s d”))
    (.mkPi (“f. ∃ s < f, ∃ d < f, !padGraph.graphDelta.pi f s d ∧ !(checkPi T)s d”))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

private def padCode (s d : M) : M :=
  qqAnd s
    (qqOr
      (Bootstrapping.ObjectArithmetic.qqEQ (Bootstrapping.ObjectArithmetic.numeral d)
        (Bootstrapping.ObjectArithmetic.numeral d))
      (Bootstrapping.ObjectArithmetic.qqNEQ (Bootstrapping.ObjectArithmetic.numeral d)
        (Bootstrapping.ObjectArithmetic.numeral d)))

private instance pad_defined : Σ₁-Function₂ (padCode : M → M → M) via padGraph :=
  .mk (by intro v; simp [padGraph, padCode])

private instance pad_delta_defined :
    ∆₁-Function₂ (padCode : M → M → M) via padGraph.graphDelta :=
  pad_defined.graph_delta

private theorem checkSigma_eval (T : ArithmeticTheory) (s d : M) :
    (checkSigma T).val.Evalb ![s, d] ↔
      Bootstrapping.Proof 𝐏𝐀 d
        (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜axiomFormula T⌝ : M)) :=
  by simp [checkSigma]

private theorem checkPi_eval (T : ArithmeticTheory) (s d : M) :
    (checkPi T).val.Evalb ![s, d] ↔
      Bootstrapping.Proof 𝐏𝐀 d
        (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜axiomFormula T⌝ : M)) :=
  by simp [checkPi]

private instance checkSigma_defined (T : ArithmeticTheory) :
    Σ₁-Relation
      (fun s d : M =>
        Bootstrapping.Proof 𝐏𝐀 d
          (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜axiomFormula T⌝ : M))) via
      checkSigma T :=
  .mk (by intro v; simp [checkSigma])

private instance checkPi_defined (T : ArithmeticTheory) :
    Π₁-Relation
      (fun s d : M =>
        Bootstrapping.Proof 𝐏𝐀 d
          (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜axiomFormula T⌝ : M))) via
      checkPi T :=
  .mk (by intro v; simp [checkPi])

theorem characteristic_proper (T : ArithmeticTheory) : (characteristic T).ProperOn M :=
  by
  intro v
  simp only [characteristic, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.pi_mkDelta]
  simp

private theorem characteristic_eval (T : ArithmeticTheory) (f : M) :
    (characteristic T).val.Evalb ![f] ↔
      ∃ s < f,
        ∃ d < f,
          f = padCode s d ∧
            Bootstrapping.Proof 𝐏𝐀 d
              (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜axiomFormula T⌝ : M)) :=
  by simp [characteristic]

/-- Axioms accompanied by numerical PA derivations of their membership in the
represented r.e. axiom set. The padding carries the derivation code. -/
def presentation (T : ArithmeticTheory) : ArithmeticTheory :=
  {τ |
    ∃ σ : ArithmeticSentence,
      ∃ d : ℕ,
        Bootstrapping.Proof 𝐏𝐀 d
            (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral (⌜σ⌝ : ℕ))
              (⌜axiomFormula T⌝ : ℕ)) ∧
          τ = padded σ d}

private theorem numeral_substitution_quote (φ : ArithmeticSemisentence 1) (s : ℕ) :
    substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜φ⌝ : ℕ) =
      (⌜(φ/[s] : ArithmeticSentence)⌝ : ℕ) :=
  by
  simp [substs1, Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]

private theorem proof_substitution_iff (φ : ArithmeticSemisentence 1) (s : ℕ) :
    (∃ d : ℕ,
        Bootstrapping.Proof 𝐏𝐀 d
          (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜φ⌝ : ℕ))) ↔
      𝐏𝐀 ⊢ (φ/[s] : ArithmeticSentence) :=
  by
  rw [numeral_substitution_quote φ s]
  exact Bootstrapping.provable_iff_provable

private theorem axiom_proof_iff (T : ArithmeticTheory) (hT : REPred (AxiomCodes T)) (s : ℕ) :
    (∃ d : ℕ,
        Bootstrapping.Proof 𝐏𝐀 d
          (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral s) (⌜axiomFormula T⌝ : ℕ))) ↔
      AxiomCodes T s :=
  (proof_substitution_iff (axiomFormula T) s).trans
    (rePred_weak_representation (T := 𝐏𝐀) hT).symm

private theorem original_axiom (T : ArithmeticTheory) (hT : REPred (AxiomCodes T))
    (σ : ArithmeticSentence) (d : ℕ)
    (hd :
      Bootstrapping.Proof 𝐏𝐀 d
        (substs1 ℒₒᵣ (Bootstrapping.ObjectArithmetic.numeral (⌜σ⌝ : ℕ))
          (⌜axiomFormula T⌝ : ℕ))) :
    σ ∈ T := by
  have h := (axiom_proof_iff T hT (⌜σ⌝ : ℕ)).mp ⟨d, hd⟩
  simpa [AxiomCodes] using h

private theorem padded_provable (T : ArithmeticTheory) (σ : ArithmeticSentence) (d : ℕ) :
    T ⊢ padded σ d ↔ T ⊢ σ := by
  unfold padded
  constructor
  · exact K_left
  · intro h
    have ht : T ⊢ ((“!!(d) = !!(d)”) ⋎ (“!!(d) ≠ !!(d)”) : ArithmeticSentence) :=
      by
      have hn :
        (“!!(d) ≠ !!(d)” : ArithmeticSentence) = ∼(“!!(d) = !!(d)” : ArithmeticSentence) := rfl
      rw [hn]
      cl_prover
    exact K_intro h ht

/-- Every padded axiom is provable in the original theory. -/
theorem presentation_weaker (T : ArithmeticTheory) (hT : REPred (AxiomCodes T)) :
    presentation T ≼ T := by
  apply WeakerThan.ofAxmProof
  intro τ hτ
  obtain ⟨σ, d, hd, rfl⟩ := hτ
  exact (padded_provable T σ d).mpr (by_axm (original_axiom T hT σ d hd))

/-- Every original axiom has a padded representative from which it follows. -/
theorem original_weaker (T : ArithmeticTheory) (hT : REPred (AxiomCodes T)) :
    T ≼ presentation T := by
  apply WeakerThan.ofAxmProof
  intro σ hσ
  obtain ⟨d, hd⟩ := (axiom_proof_iff T hT (⌜σ⌝ : ℕ)).mpr ⟨σ, rfl, hσ⟩
  apply (padded_provable (presentation T) σ d).mp
  exact by_axm (show padded σ d ∈ presentation T from ⟨σ, d, hd, rfl⟩)

private theorem padCode_lt_left (s d : M) : s < padCode s d :=
  lt_KProof_left _ _

private theorem padCode_lt_right (s d : M) : d < padCode s d := by
  exact
    lt_of_le_of_lt (Bootstrapping.ObjectArithmetic.le_numeral_self d)
      (lt_trans (Bootstrapping.ObjectArithmetic.lt_qqEQ_left _ _)
        (lt_trans (lt_or_left _ _) (lt_KProof_right _ _)))

private theorem padded_quote (σ : ArithmeticSentence) (d : ℕ) :
    (⌜padded σ d⌝ : ℕ) = padCode (⌜σ⌝ : ℕ) d := by simp [padded, padCode, Sentence.quote_eq]

private theorem padded_bounds (σ : ArithmeticSentence) (d : ℕ) :
    (⌜σ⌝ : ℕ) < (⌜padded σ d⌝ : ℕ) ∧ d < (⌜padded σ d⌝ : ℕ) :=
  by
  rw [padded_quote]
  exact ⟨padCode_lt_left _ _, padCode_lt_right _ _⟩

theorem characteristic_mem_iff (T : ArithmeticTheory) (hT : REPred (AxiomCodes T))
    (φ : Proposition ℒₒᵣ) :
    (characteristic T).val.Evalb ![(⌜φ⌝ : ℕ)] ↔ ∃ τ ∈ presentation T, φ = τ :=
  by
  rw [characteristic_eval]
  constructor
  · rintro ⟨s, _, d, _, heq, hp⟩
    obtain ⟨σ, hσ, _⟩ := (axiom_proof_iff T hT s).mp ⟨d, hp⟩
    rcases hσ with rfl
    refine ⟨padded σ d, ⟨σ, d, hp, rfl⟩, ?_⟩
    apply (Semiformula.quote_inj_iff (V := ℕ)).mp
    exact heq.trans (padded_quote σ d).symm
  · rintro ⟨τ, ⟨σ, d, hp, rfl⟩, rfl⟩
    exact ⟨(⌜σ⌝ : ℕ), (padded_bounds σ d).1, d, (padded_bounds σ d).2, padded_quote σ d, hp⟩

/-- The padded presentation has a characteristic formula whose Sigma-one and
Pi-one forms are provably equivalent in IΣ1. -/
abbrev presentationDelta1 (T : ArithmeticTheory) (hT : REPred (AxiomCodes T)) :
    (presentation T).Δ₁ where
  ch := characteristic T
  mem_iff φ := characteristic_mem_iff T hT φ
  isDelta1 :=
    HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _
      (fun V _ _ => characteristic_proper (M := V) T)

/-- Every arithmetic theory with r.e. axiom codes has an equivalent
Delta-one presentation. No soundness or consistency assumption on T is used. -/
theorem exists_craig_presentation (T : ArithmeticTheory) (hT : REPred (AxiomCodes T)) :
    ∃ S : ArithmeticTheory, Nonempty S.Δ₁ ∧ S ≼ T ∧ T ≼ S :=
  ⟨presentation T, ⟨presentationDelta1 T hT⟩, presentation_weaker T hT, original_weaker T hT⟩

end

end CraigPresentation
end FailureOfComposition

end

end PointwiseComposition

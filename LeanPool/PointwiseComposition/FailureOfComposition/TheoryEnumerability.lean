/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ProductiveDivergence
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Enumerability of deductive closure from enumerability of the axioms.
The general result uses pure-logic proofs of finite implications and does not
assume a Delta-one presentation of the given theory. -/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment

open Encodable

namespace FailureOfComposition

noncomputable section

/-- Numerical codes of axioms, using the same sentence coding as TheoremCodes. -/
def AxiomCodes (T : ArithmeticTheory) (n : ℕ) : Prop :=
  ∃ σ : ArithmeticSentence, (⌜σ⌝ : ℕ) = n ∧ σ ∈ T

/-- Provability in a Delta-one-presented theory is enumerable on sentences. -/
theorem sentence_provability_re_of_delta1 (T : ArithmeticTheory) [T.Δ₁] :
    REPred (fun σ : ArithmeticSentence => T ⊢ σ) :=
  by
  have hp : REPred (fun n : ℕ => Bootstrapping.Provable T n) :=
    rePred_iff_sigma1.mpr (by definability)
  apply REPred.of_eq (hp.comp Computable.encode)
  intro σ
  simpa only [← Sentence.quote_eq_encode_nat] using
    (Bootstrapping.provable_iff_provable (T := T) (φ := σ))

private theorem theorem_codes_re_of_sentence_provability (T : ArithmeticTheory)
    (hT : REPred (fun σ : ArithmeticSentence => T ⊢ σ)) : REPred (TheoremCodes T) :=
  by
  have he : REPred (fun p : ℕ × ArithmeticSentence => encode p.2 = p.1) :=
    (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst).computablePred.to_re
  apply
    REPred.of_eq
      ((PointwiseComposition.REPred.projection
        ((PointwiseComposition.REPred.and he) (hT.comp Computable.snd))))
  intro n
  simp only [TheoremCodes, Sentence.quote_eq_encode_nat]

/-- Theorem codes are enumerable for every Foundation Delta-one presentation. -/
theorem theorem_codes_re_of_delta1 (T : ArithmeticTheory) [T.Δ₁] : REPred (TheoremCodes T) :=
  theorem_codes_re_of_sentence_provability T (sentence_provability_re_of_delta1 T)

/-- Finite lists of elements of an enumerable predicate can be enumerated. -/
private theorem re_forall_mem_list {α : Type*} [Primcodable α] [Inhabited α] {p : α → Prop}
    (hp : REPred p) : REPred (fun l : List α => ∀ a ∈ l, p a) :=
  by
  obtain ⟨f, hf, hfp⟩ := REPred.iff'.mp hp
  let test (l : List α) (n : ℕ) : Part Unit :=
    Nat.rec (Part.some ()) (fun i r => r.bind (fun _ => f (l.getD i default))) n
  have ht : Partrec (fun l : List α => test l l.length) := by
    exact
      Partrec.nat_rec Computable.list_length (Partrec.const' (Part.some ()))
        ((hf.comp
            ((Primrec.list_getD default).to_comp.comp Computable.fst
              (Computable.fst.comp Computable.snd))).to₂)
  have htest (l : List α) (n : ℕ) : (test l n).Dom ↔ ∀ i < n, p (l.getD i default) := by
    induction n with
    | zero => simp [test]
    | succ n ih =>
      change (∃ _ : (test l n).Dom, (f (l.getD n default)).Dom) ↔ _
      simp only [exists_prop, ih, ← hfp, Nat.forall_lt_succ_right]
  apply REPred.of_eq ht.dom_re
  intro l
  rw [htest]
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    simpa only [List.getD_eq_getElem l default hi] using h i hi
  · intro h i hi
    rw [List.getD_eq_getElem l default hi]
    exact h _ (List.getElem_mem hi)

private theorem computable_list_foldl {α β : Type*} [Primcodable α] [Primcodable β]
    (f : β → α → β) (hf : Computable₂ f) :
    Computable₂ (fun l : List α => fun b : β => l.foldl f b) :=
  by
  let G (s : β × List α) : β × List α := s.2.head?.elim s (fun a => (f s.1 a, s.2.tail))
  have hG : Computable G :=
    by
    apply
      (Computable.option_casesOn (Primrec.list_head?.to_comp.comp Computable.snd) Computable.id
          ((Computable.pair (hf.comp (Computable.fst.comp Computable.fst) Computable.snd)
              (Primrec.list_tail.to_comp.comp (Computable.snd.comp Computable.fst))).to₂)).of_eq
    intro s
    dsimp only [G]
    cases s.2.head? <;> rfl
  have hiter : Computable (fun p : List α × β => G^[p.1.length] (p.2, p.1)) :=
    by
    have hh :=
      Computable.nat_rec (Computable.list_length.comp (Computable.fst (α := List α) (β := β)))
        (Computable.pair Computable.snd Computable.fst)
        ((hG.comp (Computable.snd.comp Computable.snd)).to₂)
    apply hh.of_eq
    intro p
    induction p.1.length with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih]
  have hspec : ∀ n (l : List α) (b : β), G^[n] (b, l) = ((l.take n).foldl f b, l.drop n) :=
    by
    intro n
    induction n with
    | zero => intro l b; rfl
    | succ n ih =>
      intro l b
      simp only [Function.iterate_succ, Function.comp_apply]
      cases l with
      | nil =>
        simpa only [G, List.head?_nil, Option.elim_none, List.take_nil, List.foldl_nil,
          List.drop_nil] using ih [] b
      | cons a l =>
        simpa only [G, List.head?_cons, Option.elim_some, List.tail_cons, List.take_succ_cons,
          List.drop_succ_cons, List.foldl_cons] using ih l (f b a)
  apply (Computable.fst.comp hiter).of_eq
  intro p
  rw [hspec, List.take_length]

private def finiteImplication (l : List ArithmeticSentence) (σ : ArithmeticSentence) :
    ArithmeticSentence :=
  l.foldl (fun ψ φ => φ ⇒ₗ ψ) σ

private theorem implication_computable : Computable₂ (fun σ τ : ArithmeticSentence => σ ⇒ₗ τ) :=
  by
  have hi : Computable₂ (fun n m : ℕ => Bootstrapping.imp ℒₒᵣ n m) :=
    computable₂_iff_sigma1.mpr (by definability)
  apply Computable.encode_iff.mp
  apply
    (hi.comp (Computable.encode.comp Computable.fst)
        (Computable.encode.comp Computable.snd)).of_eq
  intro p
  simp [← Sentence.quote_eq_encode_nat, Sentence.quote_def, Semiformula.quote_def]

private theorem finiteImplication_computable : Computable₂ finiteImplication :=
  computable_list_foldl _ (implication_computable.comp Computable.snd Computable.fst)

private theorem finiteImplication_provable_iff (l : List ArithmeticSentence)
    (T : ArithmeticTheory) (σ : ArithmeticSentence) :
    T ⊢ finiteImplication l σ ↔ (T ∪ {τ | τ ∈ l}) ⊢ σ := by
  induction l generalizing T σ with
  | nil => simp [finiteImplication]
  | cons φ l ih =>
    change T ⊢ finiteImplication l (φ ⇒ₗ σ) ↔ _
    rw [ih, ← deduction_iff]
    have he : adjoin φ (T ∪ {τ | τ ∈ l}) = T ∪ {τ | τ ∈ φ :: l} :=
      by
      ext τ
      simp [Set.mem_union, or_assoc, or_comm]
    rw [he]

private theorem provable_iff_finiteImplication (T : ArithmeticTheory) (σ : ArithmeticSentence) :
    T ⊢ σ ↔
      ∃ l : List ArithmeticSentence,
        (∀ τ ∈ l, τ ∈ T) ∧ (∅ : ArithmeticTheory) ⊢ finiteImplication l σ :=
  by
  constructor
  · rintro ⟨b⟩
    refine ⟨b.axioms.toList, ?_, ?_⟩
    · intro τ hτ
      exact b.axioms_mem τ (by simpa using hτ)
    rw [finiteImplication_provable_iff]
    simpa only [Set.empty_union, Multiset.mem_toList] using
      (show ({τ | τ ∈ b.axioms} : ArithmeticTheory) ⊢ σ from
        ⟨⟨b.axioms, by simp, b.derivation⟩⟩)
  · rintro ⟨l, hl, hp⟩
    rw [finiteImplication_provable_iff] at hp
    exact
      Entailment.wkProof
        (by
          intro τ hτ
          exact hl τ (by simpa only [Set.empty_union, Set.mem_ofPred_eq] using hτ))
        hp

/-- Recursively enumerable axiom codes yield recursively enumerable theorem
codes. The theory need not have a Delta-one presentation. -/
theorem theorem_codes_re_of_axiom_codes (T : ArithmeticTheory) (hT : REPred (AxiomCodes T)) :
    REPred (TheoremCodes T) :=
  by
  let : Inhabited ArithmeticSentence := ⟨⊤⟩
  have ha : REPred (fun σ : ArithmeticSentence => σ ∈ T) :=
    by
    apply REPred.of_eq (hT.comp Computable.encode)
    intro σ
    simp only [AxiomCodes, Sentence.quote_eq_encode_nat, Encodable.encode_inj]
    simp
  have hl : REPred (fun l : List ArithmeticSentence => ∀ σ ∈ l, σ ∈ T) := re_forall_mem_list ha
  have hp := sentence_provability_re_of_delta1 (∅ : ArithmeticTheory)
  have hh :
    REPred
      (fun p : ArithmeticSentence × List ArithmeticSentence =>
        (∀ σ ∈ p.2, σ ∈ T) ∧ (∅ : ArithmeticTheory) ⊢ finiteImplication p.2 p.1) :=
    (PointwiseComposition.REPred.and (hl.comp Computable.snd))
      (hp.comp (finiteImplication_computable.comp Computable.snd Computable.fst))
  apply theorem_codes_re_of_sentence_provability T
  apply REPred.of_eq (PointwiseComposition.REPred.projection hh)
  intro σ
  exact (provable_iff_finiteImplication T σ).symm

end

end FailureOfComposition

end

end PointwiseComposition

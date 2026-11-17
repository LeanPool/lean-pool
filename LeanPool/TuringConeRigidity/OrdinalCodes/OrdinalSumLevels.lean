/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalSumLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumClosure
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderTypeLevels

/-!
# Ordinal Sum Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem ordinal_add_relative (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ relativeModel M R) (hb : b.toZFSet ∈ relativeModel M R) :
    (a+b).toZFSet ∈ relativeModel M R ∧ ∃ f ∈ relativeModel M R,
      OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
        (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f :=
  ordinal_add_internal_schemas _ (relativeModel_transitive M R hM)
    (relativeModel_pairing M R hM hT hR) (relativeModel_union M R hM hT hR)
    (relativeModel_power_set M R hM hT hR) (relativeModel_bounded_separation M R hM hT hR)
    (relativeModel_sigma_replacement M R hM hT hR)
    ((mem_relativeModel M R _ hM hT hR).mpr (empty_in_relativeModel M R hM hT)) a b ha hb

theorem sum_sentence_at_levels (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ relativeModel M R) (hb : b.toZFSet ∈ relativeModel M R) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      a.toZFSet ∈ level R δ ∧ b.toZFSet ∈ level R δ ∧ (a+b).toZFSet ∈ level R δ ∧
      (∃ f ∈ level R δ, OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
        (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f) ∧
      ∀ z ∈ level R δ, sumSentence.Sat (level R δ : Set ZFSet)
        (cons z (cons a.toZFSet (fun _ => b.toZFSet))) ↔ z = (a+b).toZFSet := by
  let N := relativeModel M R
  have hN := relativeModel_transitive M R hM
  have hP := relativeModel_pairing M R hM hT hR
  have hU := relativeModel_union M R hM hT hR
  have hPow := relativeModel_power_set M R hM hT hR
  have hS := relativeModel_bounded_separation M R hM hT hR
  have h0 : (∅ : ZFSet.{u}) ∈ N :=
    (mem_relativeModel M R _ hM hT hR).mpr (empty_in_relativeModel M R hM hT)
  have h1 := singleton_mem N hN hP h0
  have hd := sumDomain_mem N _ _ hN hP hU hPow hS h0 ha hb
  have hr := sumRelation_mem N _ _ hN hP hU hPow hS h0 ha hb
  obtain ⟨hc,f,hf,hcert⟩ := ordinal_add_relative M R hM hT hR a b ha hb
  let e := cons a.toZFSet (cons b.toZFSet (cons (a+b).toZFSet
    (cons (sumDomain a.toZFSet b.toZFSet) (cons (sumRelation a.toZFSet b.toZFSet)
      (cons ∅ (cons ({∅} : ZFSet.{u}) (fun _ => f)))))))
  have he (i : ℕ) : e i ∈ N := by
    rcases i with _|_|_|_|_|_|_|i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact hr
    · exact h0
    · exact h1
    · exact hf
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 8
    (fun i _ => (mem_relativeModel M R _ hM hT hR).mp (he i))
  refine ⟨γ,hγ,?_⟩
  intro δ hδ
  have hL (i : ℕ) (hi : i < 8) : e i ∈ level R δ := level_mono R hδ (hγe i hi)
  refine ⟨hL 0 (by omega),hL 1 (by omega),hL 2 (by omega),
    ⟨f,hL 7 (by omega),hcert⟩,?_⟩
  intro z hz
  exact sumSentence_spec_of_certificate (level R δ) (level_transitive R δ)
    (cons z (cons a.toZFSet (fun _ => b.toZFSet)))
    (by intro i; rcases i with _|_|i
        · exact hz
        · exact hL 0 (by omega)
        · exact hL 1 (by omega)) a b rfl rfl
    (hL 5 (by omega)) (hL 6 (by omega)) (hL 3 (by omega)) (hL 4 (by omega))
    ⟨f,hL 7 (by omega),hcert⟩

end TuringRigidity.OrdinalArithmetic

end OAI

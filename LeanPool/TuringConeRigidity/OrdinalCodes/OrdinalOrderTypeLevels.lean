/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalOrderTypeLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelPower
public import LeanPool.TuringConeRigidity.Constructibility.RelativeSigmaSchemas
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalOrderTypeSyntax

/-!
# Ordinal Order Type Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel RelationCollapse
universe u

theorem orderType_certificate_relative (M R d r : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (hd : d ∈ relativeModel M R) (hr : r ∈ relativeModel M R)
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ relativeModel M R ∧
      ∃ f ∈ relativeModel M R, OrderTypeCertificate d r (orderType d r wf).toZFSet f := by
  obtain ⟨ha,f,hf,hg,ho⟩ := orderType_internal (relativeModel M R) d r
    (relativeModel_transitive M R hM) (relativeModel_pairing M R hM hT hR)
    (relativeModel_union M R hM hT hR) (relativeModel_power_set M R hM hT hR)
    (relativeModel_bounded_separation M R hM hT hR)
    (relativeModel_sigma_replacement M R hM hT hR) hd hr wf ht
  exact ⟨ha,f,hf,ZFSet.isOrdinal_toZFSet _,hg,ho⟩

theorem orderType_sentence_at_levels (M R d r : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (hd : d ∈ relativeModel M R) (hr : r ∈ relativeModel M R)
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      d ∈ level R δ ∧ r ∈ level R δ ∧ (orderType d r wf).toZFSet ∈ level R δ ∧
      (∃ f ∈ level R δ, OrderTypeCertificate d r (orderType d r wf).toZFSet f) ∧
      ∀ z ∈ level R δ,
        orderTypeSentence.Sat (level R δ : Set ZFSet) (cons z (cons d (cons r (fun _ => d)))) ↔
          z = (orderType d r wf).toZFSet := by
  obtain ⟨ha,f,hf,hc⟩ := orderType_certificate_relative M R d r hM hT hR hd hr wf ht
  let e := cons d (cons r (cons (orderType d r wf).toZFSet (fun _ => f)))
  have he (i : ℕ) : e i ∈ relativeModel M R := by
    rcases i with _|_|_|i
    · exact hd
    · exact hr
    · exact ha
    · exact hf
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 4
    (fun i _ => (mem_relativeModel M R _ hM hT hR).mp (he i))
  refine ⟨γ,hγ,?_⟩
  intro δ hδ
  have hdL : d ∈ level R δ := level_mono R hδ (hγe 0 (by omega))
  have hrL : r ∈ level R δ := level_mono R hδ (hγe 1 (by omega))
  have haL : (orderType d r wf).toZFSet ∈ level R δ := level_mono R hδ (hγe 2 (by omega))
  have hfL : f ∈ level R δ := level_mono R hδ (hγe 3 (by omega))
  refine ⟨hdL,hrL,haL,⟨f,hfL,hc⟩,?_⟩
  intro z hz
  exact orderTypeSentence_spec_of_certificate (level R δ) (level_transitive R δ)
    (cons z (cons d (cons r (fun _ => d)))) (by
      intro i; rcases i with _|_|_|i
      · exact hz
      · exact hdL
      · exact hrL
      · exact hdL) wf ht ⟨f,hfL,hc⟩

end TuringRigidity.RelativeConstructible

end OAI

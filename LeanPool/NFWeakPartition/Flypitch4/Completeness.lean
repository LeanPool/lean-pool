/-
Copyright (c) 2019 Jesse Michael Han and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han, Floris van Doorn, and Flypitch4 contributors
-/

module

/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/completeness.lean (59 lines) — Task 20

public import LeanPool.NFWeakPartition.Flypitch4.Henkin

/-! NF weak partition development: Flypitch4.Completeness. -/


public section

namespace NFChoice

namespace Fol

open Lhom

universe u

variable {L : Language.{u}}

/-! ## satisfied_of_provable
Soundness: provability implies semantic consequence.
-/


lemma satisfied_of_provable (T : SentTheory L) (ψ : sentence L) (h : T ⊢ₛ' ψ) :
    ssatisfied T ψ :=
  ssatisfied_soundness h

/-! ## completeness_for_inconsistent_theories
For an inconsistent theory, provability and semantic entailment
coincide trivially.
-/


lemma completeness_for_inconsistent_theories (T : SentTheory L) (ψ : sentence L)
    (h_inconsis : ¬T.is_consistent) : (T ⊢ₛ' ψ) ↔ ssatisfied T ψ :=
  by
  constructor
  · intro h; exact satisfied_of_provable T ψ h
  · intro
      _
        -- T is inconsistent means T ⊢ₛ' bd_falsum

    have h_prov : T ⊢ₛ' (bd_falsum : sentence L) :=
      by
      simp only [SentTheory.is_consistent, not_not] at h_inconsis
      exact h_inconsis
    exact sfalsumE h_prov

/-! ## model_existence
T is consistent iff there is a nonempty model of T.
-/


theorem model_existence (T : SentTheory L) :
    T.is_consistent ↔ ∃ M : Structure L, Nonempty M.carrier ∧ all_realize_sentence M T :=
  by
  constructor
  · intro hT
    let M' :=
      term_model (completion_of_henkinization_complete hT)
        (completion_of_henkinization_is_henkin hT)
    let M : Structure L := Lhom.reduct (henkin_language_canonical_map 0) M'
    refine ⟨M, ?_, ?_⟩
    ·
      -- nonemptiness: term_model' T = Quotient (closed_term L) (term_setoid T) is nonempty
            -- We get a constant from has_enough_constants: use bd_const c as
            -- a witness

      rw [show M.carrier = M'.carrier from Lhom.reduct_coe M']
      change Nonempty (term_model' (completion_of_henkinization hT))
      obtain ⟨C, _⟩ := completion_of_henkinization_is_henkin hT
      exact ⟨@Quotient.mk'' _ (term_setoid _) (bd_const (C bd_falsum))⟩
    · -- T satisfaction
      exact reduct_of_complete_henkinization_models_T hT
  · intro h_ex
    obtain ⟨M, H_nonempty, H_sat⟩ := h_ex
    intro h_prov
    have : ssatisfied T (bd_falsum : sentence L) := ssatisfied_soundness h_prov
    exact (this H_nonempty H_sat).elim

/-! ## nonempty_model_of_consis
A consistent theory has a nonempty model.
-/


@[expose]
noncomputable def nonempty_model_of_consis {T : SentTheory L} (hT : T.is_consistent) :
    Σ' M : Structure L, Nonempty M.carrier ∧ all_realize_sentence M T :=
  by
  have := (model_existence T).mp hT
  exact ⟨this.choose, this.choose_spec.1, this.choose_spec.2⟩

/-! ## completeness
The Gödel completeness theorem: T ⊢ₛ' ψ ↔ ssatisfied T ψ.
-/


theorem completeness (T : SentTheory L) (ψ : sentence L) : (T ⊢ₛ' ψ) ↔ ssatisfied T ψ :=
  by
  constructor
  · exact satisfied_of_provable T ψ
  · intro H
    by_contra h_not_prov
    have h_consis : (insert (bd_not ψ) T).is_consistent :=
      consis_not_of_not_provable h_not_prov
    obtain ⟨M, H_nonempty, H_sat⟩ := nonempty_model_of_consis h_consis
    have H_T : all_realize_sentence M T :=
      all_realize_sentence_of_subset H_sat
        (Set.subset_insert _ _)
          -- M satisfies ψ (from the semantic entailment hypothesis)

    have H_ψ : M ⊨ₘ ψ := H H_nonempty H_T
    have H_nψ : M ⊨ₘ (bd_not ψ : sentence L) :=
      H_sat
        (Set.mem_insert _ _)
          -- Contradiction: ψ and ¬ψ both hold

    simp only [realize_sentence_not] at H_nψ
    exact H_nψ H_ψ

/-! ## compactness
Semantic compactness: T ⊨ f iff some finite subset of T
semantically entails f.
-/


theorem compactness {T : SentTheory L} {f : sentence L} :
    ssatisfied T f ↔
      ∃ fs : Finset (sentence L),
        ssatisfied (fs : Set (sentence L)) f ∧ (fs : Set (sentence L)) ⊆ T :=
  by
  rw [← completeness T f, theory_proof_compactness_iff]
  constructor
  · rintro
      ⟨Γ, hΓ, hΓ_sub⟩
          -- hΓ : Γ ⊢ₛ' f; convert to ssatisfied using completeness

    exact ⟨Γ, (completeness (Γ : Set (sentence L)) f).mp hΓ, hΓ_sub⟩
  · rintro
      ⟨Γ, hΓ, hΓ_sub⟩
          -- hΓ : ssatisfied Γ f; convert to ⊢ₛ' using completeness

    exact ⟨Γ, (completeness (Γ : Set (sentence L)) f).mpr hΓ, hΓ_sub⟩

end Fol

end NFChoice

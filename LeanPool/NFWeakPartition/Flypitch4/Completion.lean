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
/- Lean 4 port of src/completion.lean — every consistent theory
extends to a complete one -/

public import LeanPool.NFWeakPartition.Flypitch4.Compactness
public import Mathlib.Order.Zorn

/-! NF weak partition development: Flypitch4.Completion. -/


public section

namespace NFChoice

open NFChoice.Set

namespace Fol

universe u v

variable {L : Language.{u}}

/-! ## Helper lemmas at the sentence level -/


/-- A sentence-level axiom rule: if ψ ∈ T (as a SentTheory), then
T ⊢ₛ' ψ -/
lemma saxm' {T : SentTheory L} {ψ : sentence L} (h : ψ ∈ T) : T ⊢ₛ' ψ :=
  ⟨prf.axm (Set.mem_image_of_mem _ h)⟩

/-- Sentence-level weakening for sprovable -/
lemma sweakening' {T T' : SentTheory L} (h_sub : T ⊆ T') {ψ : sentence L} (h : T ⊢ₛ' ψ) :
    T' ⊢ₛ' ψ :=
  weakening' (Set.image_mono h_sub) h

/-- snot_and_self: from T ⊢ₛ' ψ and T ⊢ₛ' ∼ᵇψ, derive T ⊢ₛ'
bd_falsum -/
lemma snot_and_self'' {T : SentTheory L} {ψ : sentence L} (H₁ : T ⊢ₛ' ψ)
    (H₂ : T ⊢ₛ' bd_not ψ) : T ⊢ₛ' bd_falsum :=
  -- bd_not ψ = bd_imp ψ bd_falsum, so (bd_not ψ).fst = ψ.fst ⟹ ⊥'

  impE' _ H₂ H₁

/-- sfalsumE: from T ⊢ₛ' bd_falsum derive T ⊢ₛ' ψ (ex falso) -/
lemma sfalsumE {T : SentTheory L} {ψ : sentence L} (h : T ⊢ₛ' bd_falsum) : T ⊢ₛ' ψ :=
  by
  apply falsumE'
  exact weakening1' h

/-- Sentence-level simpI: T ⊢ₛ' ψ → insert ϕ T ⊢ₛ' ψ -/
lemma simpI {T : SentTheory L} {ψ ϕ : sentence L} (h : T ⊢ₛ' ψ) : insert ϕ T ⊢ₛ' ψ :=
  sweakening' (Set.subset_insert ϕ T) h

/-! ## Helper: (insert ψ T).fst = insert ψ.fst T.fst -/


private lemma sentTheory_insert_fst (ψ : sentence L) (T : SentTheory L) :
    (insert ψ T).fst = insert ψ.fst T.fst := by simp [SentTheory.fst, Set.image_insert_eq]

private lemma sentTheory_insert_bd_not_fst (ψ : sentence L) (T : SentTheory L) :
    (insert (bd_not ψ) T).fst = insert (∼ψ.fst) T.fst := by
  simp only [SentTheory.fst, Set.image_insert_eq, bounded_preformula.fst_bd_not]

/-! ## consis_not_of_not_provable and inconsis_not_of_provable -/


/-- If T ⊬ₛ' f, then T ∪ {∼ᵇf} is consistent -/
lemma consis_not_of_not_provable {T : SentTheory L} {f : sentence L} (h : ¬T ⊢ₛ' f) :
    (insert (bd_not f) T).is_consistent :=
  by
  simp only [SentTheory.is_consistent]
  intro hc
  apply h
  rw [sentTheory_insert_bd_not_fst] at hc
  exact falsumE' hc

/-- If T ⊢ₛ' f, then T ∪ {∼ᵇf} is inconsistent -/
lemma inconsis_not_of_provable {T : SentTheory L} {f : sentence L} (H : T ⊢ₛ' f) :
    ¬(insert (bd_not f) T).is_consistent :=
  by
  intro hcons
  have h1 : insert (bd_not f) T ⊢ₛ' f := simpI H
  have h2 : insert (bd_not f) T ⊢ₛ' bd_not f := saxm' (Set.mem_insert _ _)
  exact hcons (snot_and_self'' h1 h2)

/-- If T ∪ {∼ᵇf} is inconsistent, then T ⊢ₛ' f -/
lemma provable_of_inconsis_not {T : SentTheory L} {f : sentence L}
    (h : ¬(insert (bd_not f) T).is_consistent) : T ⊢ₛ' f :=
  by
  by_contra hnot
  exact h (consis_not_of_not_provable hnot)

/-! ## can_extend: one of T ∪ {ψ} or T ∪ {∼ᵇψ} is consistent -/


/-- Given a consistent theory T and a sentence ψ, either T ∪ {ψ}
or T ∪ {∼ᵇψ} is consistent -/
lemma can_extend (T : SentTheory L) (ψ : sentence L) (h : T.is_consistent) :
    (insert ψ T).is_consistent ∨ (insert (bd_not ψ) T).is_consistent :=
  by
  by_contra hall
  simp only [not_or] at hall
  obtain ⟨H1, H2⟩ := hall
  have hnotpsi : T ⊢ₛ' bd_not ψ :=
    by
    simp only [SentTheory.is_consistent, not_not] at H1
    rw [sentTheory_insert_fst] at H1
    simp only [SentTheory.sprovable, SentTheory.fst, bd_not, bounded_preformula.fst]
    exact impI' H1
  have hpsi : T ⊢ₛ' ψ := provable_of_inconsis_not H2
  exact h (snot_and_self'' hpsi hnotpsi)

/-! ## Theory_over: the poset of consistent extensions of T -/


/-- Theory_over T hT: the subtype of SentTheory L consisting of
consistent theories ⊇ T -/
@[expose]
def Theory_over (T : SentTheory L) (_hT : T.is_consistent) : Type u :=
  { T' : SentTheory L // T ⊆ T' ∧ T'.is_consistent }

/-- T itself is a Theory_over T hT -/
@[expose]
def over_self (T : SentTheory L) (hT : T.is_consistent) : Theory_over T hT :=
  ⟨T, le_refl _, hT⟩

/-- Subset order on Theory_over T hT -/
@[expose]
def Theory_over_subset {T : SentTheory L} {hT : T.is_consistent} :
    Theory_over T hT → Theory_over T hT → Prop := fun T1 T2 => T1.val ⊆ T2.val

instance {T : SentTheory L} {hT : T.is_consistent} : HasSubset (Theory_over T hT) :=
  ⟨Theory_over_subset⟩

instance {T : SentTheory L} {hT : T.is_consistent} : Nonempty (Theory_over T hT) :=
  ⟨over_self T hT⟩

/-! ## consis_limit: the limit of a chain is consistent -/
-- Helper: Theory_over_subset is transitive


-- Helper: Theory_over_subset is transitive
private lemma TO_trans {T : SentTheory L} {hT : T.is_consistent}
    {a b c : Theory_over T hT} (hab : Theory_over_subset a b)
    (hbc : Theory_over_subset b c) : Theory_over_subset a c := fun _x hx =>
  hbc
    (hab hx)
      -- Helper: move from one theory's fst to another's via subset


-- Helper: move from one theory's fst to another's via subset
private lemma TO_fst_subset {T : SentTheory L} {hT : T.is_consistent}
    {a b : Theory_over T hT} (h : Theory_over_subset a b) {f : formula L}
    (hf : f ∈ a.val.fst) : f ∈ b.val.fst :=
  by
  simp only [SentTheory.fst, Set.mem_image] at hf ⊢
  obtain ⟨s, hs, rfl⟩ := hf
  exact ⟨s, h hs, rfl⟩

/-- The union of a chain of consistent extensions of T is
consistent -/
lemma consis_limit {T : SentTheory L} {hT : T.is_consistent} (Ts : Set (Theory_over T hT))
    (h_chain : IsChain Theory_over_subset Ts) :
    (T ∪ ⋃₀ (Subtype.val '' Ts)).is_consistent :=
  by
  simp only [SentTheory.is_consistent]
  intro h_inconsis
  by_cases hne : Ts.Nonempty
  · have : DecidableEq (formula L) := fun x y => Classical.propDecidable _
    obtain ⟨Γ, H_prov, H_sub⟩ := proof_compactness h_inconsis
    have h_wit :
      ∀ f ∈ (Γ : Set (formula L)),
        f ∈ T.fst ∨ ∃ Tf : Theory_over T hT, Tf ∈ Ts ∧ f ∈ Tf.val.fst :=
      by
      intro f hf
      rcases H_sub hf with ⟨s, hs | ⟨t, ⟨Tf, hTf, rfl⟩, hst⟩, rfl⟩
      · exact Or.inl ⟨s, hs, rfl⟩
      · exact
          Or.inr
            ⟨Tf, hTf, ⟨s, hst, rfl⟩⟩
              -- Key: ∃ T_max ∈ Ts, (Γ : Set (formula L)) ⊆ T_max.val.fst
                  -- By Finset.induction on Γ, merging witnesses using the chain

    have key :
      ∀ (S : Finset (formula L)),
        (∀ f ∈ (S : Set (formula L)),
            f ∈ T.fst ∨ ∃ Tf : Theory_over T hT, Tf ∈ Ts ∧ f ∈ Tf.val.fst) →
          ∃ T_max : Theory_over T hT,
            T_max ∈ Ts ∧ (S : Set (formula L)) ⊆ T_max.val.fst :=
      by
      intro S
      induction S using Finset.induction with
      | empty => intro _; obtain ⟨m, hm⟩ := hne; exact ⟨m, hm, by simp⟩
      | insert a s hnotmem ih =>
        intro hfw
        have hfw_s :
          ∀ g ∈ (s : Set (formula L)),
            g ∈ T.fst ∨ ∃ Tf : Theory_over T hT, Tf ∈ Ts ∧ g ∈ Tf.val.fst :=
          fun g hg =>
          hfw g
            (Set.mem_of_mem_of_subset hg (Finset.coe_subset.mpr (Finset.subset_insert a s)))
        obtain ⟨T_prev, hT_prev, hs_sub⟩ := ih hfw_s
        rcases hfw a (Finset.mem_coe.mpr (Finset.mem_insert_self a s)) with haT |
          ⟨Tf, hTf, haTf⟩
        · -- a ∈ T.fst ⊆ T_prev.fst (since T ⊆ T_prev)
          refine
            ⟨T_prev, hT_prev, by
              simp only [Finset.coe_insert]
              intro g hg
              rcases Set.mem_insert_iff.mp hg with rfl | hg'
              · simp only [SentTheory.fst, Set.mem_image] at haT ⊢
                obtain ⟨s', hs', rfl⟩ := haT
                exact ⟨s', T_prev.property.1 hs', rfl⟩
              · exact hs_sub hg'⟩
        · -- a ∈ Tf.fst; merge T_prev and Tf using the chain

          rcases eq_or_ne T_prev Tf with rfl | hne_TPTf
          · -- T_prev = Tf
            exact
              ⟨T_prev, hT_prev, by
                simp only [Finset.coe_insert]
                intro g hg
                rcases Set.mem_insert_iff.mp hg with rfl | hg'
                · exact haTf
                · exact hs_sub hg'⟩
          · -- T_prev ≠ Tf: use chain to compare

            rcases h_chain hT_prev hTf hne_TPTf with h | h
            · -- Theory_over_subset T_prev Tf: Tf is bigger
              exact
                ⟨Tf, hTf, by
                  simp only [Finset.coe_insert]
                  intro g hg
                  rcases Set.mem_insert_iff.mp hg with rfl | hg'
                  · exact haTf
                  · exact TO_fst_subset h (hs_sub hg')⟩
            · -- Theory_over_subset Tf T_prev: T_prev is bigger
              exact
                ⟨T_prev, hT_prev, by
                  simp only [Finset.coe_insert]
                  intro g hg
                  rcases Set.mem_insert_iff.mp hg with rfl | hg'
                  · exact TO_fst_subset h haTf
                  · exact hs_sub hg'⟩
    obtain ⟨T_max, _, hΓ_sub⟩ := key Γ h_wit
    exact T_max.property.2 (weakening' hΓ_sub H_prov)
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    apply hT
    have :
      (T ∪ ⋃₀ ((fun a : Theory_over T hT => a.val) '' (∅ : Set (Theory_over T hT)))).fst =
        T.fst :=
      by simp [SentTheory.fst]
    exact this ▸ h_inconsis

/-! ## limit_theory: build the limit as a Theory_over -/


/-- Given a chain of consistent extensions, their union is a
consistent extension -/
@[expose]
noncomputable def limit_theory {T : SentTheory L} {hT : T.is_consistent}
    (Ts : Set (Theory_over T hT)) (h_chain : IsChain Theory_over_subset Ts) :
    Σ' (T_lim : Theory_over T hT), ∀ T' ∈ Ts, T'.val ⊆ T_lim.val :=
  by
  refine ⟨⟨T ∪ ⋃₀ (Subtype.val '' Ts), ?_, consis_limit Ts h_chain⟩, ?_⟩
  · exact Set.subset_union_left
  · intro T' hT' ψ hψ
    apply Set.mem_union_right
    refine ⟨T'.val, ?_, hψ⟩
    exact Set.mem_image_of_mem Subtype.val hT'

/-! ## can_use_zorn -/


/-- The poset of theories over T satisfies Zorn's hypotheses -/
lemma can_use_zorn {T : SentTheory L} {hT : T.is_consistent} :
    (∀ c : Set (Theory_over T hT),
        IsChain Theory_over_subset c → ∃ ub : Theory_over T hT, ∀ a ∈ c, a ⊆ ub) ∧
      (∀ (a b c : Theory_over T hT),
        Theory_over_subset a b → Theory_over_subset b c → Theory_over_subset a c) :=
  ⟨fun c h_chain => ⟨(limit_theory c h_chain).fst, (limit_theory c h_chain).snd⟩,
    fun _a _b _c hab hbc => fun _x hx => hbc (hab hx)⟩

/-! ## maximal_extension -/


/-- Given a consistent theory T, there is a maximal consistent
extension of T -/
@[expose]
noncomputable def maximal_extension (T : SentTheory L) (hT : T.is_consistent) :
    Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max :=
  by
  have htrans :
    ∀ {a b c : Theory_over T hT},
      Theory_over_subset a b → Theory_over_subset b c → Theory_over_subset a c :=
    fun hab hbc => can_use_zorn.2 _ _ _ hab hbc
  have h_zorn :
    ∃ m : Theory_over T hT,
      ∀ a : Theory_over T hT, Theory_over_subset m a → Theory_over_subset a m :=
    @exists_maximal_of_chains_bounded (Theory_over T hT) Theory_over_subset can_use_zorn.1
      @htrans
  exact ⟨h_zorn.choose, fun T' hT1 => h_zorn.choose_spec T' (fun x hx => hT1 hx)⟩

/-! ## cannot_extend_maximal_extension -/


/-- A maximal extension cannot be consistently extended by any
new sentence -/
lemma cannot_extend_maximal_extension {T : SentTheory L} {hT : T.is_consistent}
    (T_max' : Σ' (T_max : Theory_over T hT), ∀ T' : Theory_over T hT, T_max ⊆ T' → T' ⊆ T_max)
    (ψ : sentence L) (H : (insert ψ T_max'.fst.val).is_consistent)
    (H1 : ψ ∉ T_max'.fst.val) : False :=
  by
  have T_over_T : T ⊆ T_max'.fst.val := T_max'.fst.property.1
  let T_bad : Theory_over T hT :=
    ⟨insert ψ T_max'.fst.val, fun x hx => Set.mem_insert_of_mem ψ (T_over_T hx), H⟩
  have h_sub : Theory_over_subset T_max'.fst T_bad := fun x hx =>
    Set.mem_insert_of_mem ψ hx
  have h_max : Theory_over_subset T_bad T_max'.fst := T_max'.snd T_bad h_sub
  exact H1 (h_max (Set.mem_insert ψ T_max'.fst.val))

/-! ## is_complete for SentTheory -/


/-- A SentTheory is complete if it is consistent and every
sentence or its negation is in it -/
@[expose]
def SentTheory.is_complete (T : SentTheory L) : Prop :=
  T.is_consistent ∧ ∀ ψ : sentence L, ψ ∈ T ∨ bd_not ψ ∈ T

/-! ## complete_maximal_extension_of_consis -/


/-- The maximal extension of a consistent theory is complete -/
lemma complete_maximal_extension_of_consis {T : SentTheory L} {hT : T.is_consistent} :
    (maximal_extension T hT).fst.val.is_complete :=
  by
  refine ⟨(maximal_extension T hT).fst.property.right, ?_⟩
  intro ψ
  by_cases hmem : ψ ∈ (maximal_extension T hT).fst.val
  · exact Or.inl hmem
  · apply Or.inr
    by_contra hnot
    have hT_max_consis := (maximal_extension T hT).fst.property.right
    rcases can_extend (maximal_extension T hT).fst.val ψ hT_max_consis with h | h
    · exact cannot_extend_maximal_extension _ ψ h hmem
    · exact cannot_extend_maximal_extension _ (bd_not ψ) h hnot

/-! ## completion_of_consis -/


/-- Every consistent theory has a complete extension -/
@[expose]
noncomputable def completion_of_consis (T : SentTheory L) (h_consis : T.is_consistent) :
    Σ' (T' : Theory_over T h_consis), T'.val.is_complete :=
  ⟨(maximal_extension T h_consis).fst, complete_maximal_extension_of_consis⟩

end Fol

end NFChoice

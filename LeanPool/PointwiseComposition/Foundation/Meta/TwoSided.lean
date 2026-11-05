/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Propositional.Entailment.Cl

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace Entailment

open FiniteContext

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] {S : Type*}
  [Entailment S F]

variable (𝓢 : S)

/-- The Two Sided construction in `FFL.Entailment`. -/
abbrev TwoSided (Γ Δ : List F) : Prop :=
  Γ ⊢[𝓢] (PointwiseComposition.List.disj Δ)

variable {𝓢} [Entailment.Int 𝓢]

local notation:40 Γ:45 " ⟹ " Δ:46 => TwoSided 𝓢 Γ Δ

namespace TwoSided

variable {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : List F} {φ ψ χ : F}

omit [DecidableEq F] in
lemma weakening (h : Γ₁ ⟹ Δ₁) (HΓ : Γ₁ ⊆ Γ₂ := by classical simp) (HΔ : Δ₁ ⊆ Δ₂ := by simp) :
    Γ₂ ⟹ Δ₂ :=
  FiniteContext.weakening HΓ <| left_Disj_intro Δ₁ (fun _ hψ ↦ right_Disj_intro _ (HΔ hψ))⨀h

omit [DecidableEq F] in
lemma remove_left (hφ : Γ ⟹ Δ) : φ :: Γ ⟹ Δ := by classical exact weakening hφ
omit [DecidableEq F] in
lemma remove_right (hφ : Γ ⟹ Δ) : Γ ⟹ φ :: Δ := by classical exact weakening hφ
omit [DecidableEq F] in
lemma rotate_right (hφ : Γ ⟹ Δ ++ [φ]) : Γ ⟹ φ :: Δ := by classical exact weakening hφ
omit [DecidableEq F] in
lemma rotate_left (hφ : (Γ ++ [φ]) ⟹ Δ) : (φ :: Γ) ⟹ Δ := by classical exact weakening hφ
omit [DecidableEq F] in
lemma rotate_right_inv (hφ : Γ ⟹ φ :: Δ) : Γ ⟹ Δ ++ [φ] := by classical exact weakening hφ
omit [DecidableEq F] in
lemma rotate_left_inv (hφ : (φ :: Γ) ⟹ Δ) : (Γ ++ [φ]) ⟹ Δ := by
  classical
  exact
    weakening hφ
-- `DecidableEq F` is not referenced in the proof term itself, but the ambient
-- instance is needed for elaboration to disambiguate the overloaded `⨀`
-- notation; omitting it (as the `unusedSectionVars` linter suggests) breaks
-- elaboration, so the false-positive warning is suppressed here.
omit [DecidableEq F] in
lemma to_provable {φ} (h : [] ⟹ [φ]) : 𝓢 ⊢ φ := by
  classical exact FiniteContext.provable_iff_provable.mpr <| left_Disj_intro [φ] (by simp)⨀h
omit [DecidableEq F] in
lemma add_hyp {𝒯 : S} [𝒯 ≼ 𝓢] (hφ : 𝒯 ⊢ φ) (h : (φ :: Γ) ⟹ Δ) : Γ ⟹ Δ := by
  classical exact deduct h⨀of' (WeakerThan.pbl hφ)
omit [DecidableEq F] in
lemma right_closed (h : φ ∈ Γ) : Γ ⟹ φ :: Δ := by
  classical exact right_Disj_intro _ (φ := φ) (by simp)⨀(FiniteContext.by_axm h)
omit [DecidableEq F] in
lemma left_closed (h : φ ∈ Δ) : (φ :: Γ) ⟹ Δ := by
  classical exact right_Disj_intro _ (φ := φ) h⨀FiniteContext.by_axm
omit [DecidableEq F] in
lemma verum_right : Γ ⟹ ⊤ :: Δ := by
  classical exact right_Disj_intro _ (φ := ⊤) (by simp)⨀(by simp)
omit [DecidableEq F] in
lemma falsum_left : (⊥ :: Γ) ⟹ Δ :=
  efq⨀by_axm₀

omit [DecidableEq F] in
lemma falsum_right (h : Γ ⟹ Δ) : Γ ⟹ ⊥ :: Δ := by classical exact weakening h
omit [DecidableEq F] in
lemma verum_left (h : Γ ⟹ Δ) : (⊤ :: Γ) ⟹ Δ := by classical exact weakening h
omit [DecidableEq F] in
lemma and_right (hφ : Γ ⟹ Δ ++ [φ]) (hψ : Γ ⟹ Δ ++ [ψ]) : Γ ⟹ φ ⋏ ψ :: Δ := by
  classical
  have :
    Γ ⊢[𝓢]
      (PointwiseComposition.List.disj (φ :: Δ)) ⇒ₗ
        (PointwiseComposition.List.disj (ψ :: Δ)) ⇒ₗ
          (PointwiseComposition.List.disj (φ ⋏ ψ :: Δ)) :=
    by
    apply left_Disj_intro
    rintro χ hχ
    rcases show χ = φ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
    · apply deduct
      apply left_Disj_intro
      intro ξ hξ
      rcases show ξ = ψ ∨ ξ ∈ Δ by simpa using hξ with (rfl | hξ)
      · exact
          deduct <|
            right_Disj_intro (χ ⋏ ξ :: Δ) (φ := χ ⋏ ξ)
                List.mem_cons_self⨀(K_intro by_axm₁ by_axm₀)
      · exact right_Disj_intro _ (by simp [hξ])
    · exact deduct <| dhyp <| right_Disj_intro _ (φ := χ) (by simp [hχ])⨀by_axm₀
  exact this⨀weakening hφ⨀weakening hψ

omit [DecidableEq F] in
lemma or_left (hφ : Γ ++ [φ] ⟹ Δ) (hψ : Γ ++ [ψ] ⟹ Δ) : φ ⋎ ψ :: Γ ⟹ Δ := by
  classical
  apply deductInv
  apply left_A_intro
  · apply deduct <| weakening hφ
  · apply deduct <| weakening hψ

omit [DecidableEq F] in
lemma or_right (h : Γ ⟹ Δ ++ [φ, ψ]) : Γ ⟹ φ ⋎ ψ :: Δ := by
  classical
  have :
    Γ ⊢[𝓢]
      (PointwiseComposition.List.disj (φ :: ψ :: Δ)) ⇒ₗ
        (PointwiseComposition.List.disj (φ ⋎ ψ :: Δ)) :=
    by
    apply left_Disj_intro
    intro χ hχ
    rcases show χ = φ ∨ χ = ψ ∨ χ ∈ Δ by simpa using hχ with (rfl | rfl | hχ)
    · apply right_Disj_intro' (χ ⋎ ψ :: Δ) (φ := χ ⋎ ψ) (by simp) or₁
    · apply right_Disj_intro' (φ ⋎ χ :: Δ) (φ := φ ⋎ χ) (by simp) or₂
    · apply right_Disj_intro _ (by simp [hχ])
  exact this⨀weakening h

omit [DecidableEq F] in
lemma and_left (h : Γ ++ [φ, ψ] ⟹ Δ) : (φ ⋏ ψ :: Γ) ⟹ Δ := by
  classical
  have : φ :: ψ :: Γ ⟹ Δ := weakening h
  have : (φ ⋏ ψ :: Γ) ⊢[𝓢] ψ ⇒ₗ φ ⇒ₗ (PointwiseComposition.List.disj Δ) :=
    wkProof (by simp) (deduct <| deduct this)
  exact this⨀(deductInv and₂)⨀(deductInv and₁)

omit [DecidableEq F] in
lemma neg_right_int (h : Γ ++ [φ] ⟹ []) : Γ ⟹ ∼φ :: Δ := by
  classical
  have : φ :: Γ ⟹ [] := weakening h
  have : Γ ⊢[𝓢] ∼φ := N_iff_CO.mpr <| deduct this
  have : Γ ⟹ [∼φ] := (right_Disj_intro _ (by simp))⨀this
  exact weakening this

omit [DecidableEq F] in
omit [Entailment.Int 𝓢] in
lemma neg_right_cl [Entailment.Cl 𝓢] (h : Γ ++ [φ] ⟹ Δ) : Γ ⟹ ∼φ :: Δ := by
  classical
  have hφ : Γ ⊢[𝓢] φ ⇒ₗ (PointwiseComposition.List.disj (∼φ :: Δ)) :=
    by
    apply deduct
    suffices
      (φ :: Γ) ⊢[𝓢]
        (PointwiseComposition.List.disj Δ) ⇒ₗ (PointwiseComposition.List.disj (∼φ :: Δ))
      from this⨀weakening h
    apply left_Disj_intro
    intro ψ hψ
    apply right_Disj_intro _ (by simp [hψ])
  have hnφ : Γ ⊢[𝓢] ∼φ ⇒ₗ (PointwiseComposition.List.disj (∼φ :: Δ)) :=
    right_Disj_intro _ (by simp)
  exact left_A_intro hφ hnφ⨀lem

omit [DecidableEq F] in
lemma neg_left_int (h : Γ ++ [∼φ] ⟹ Δ ++ [φ]) : ∼φ :: Γ ⟹ Δ := by
  classical
  have h : ∼φ :: Γ ⟹ φ :: Δ := weakening h
  suffices
    (∼φ :: Γ) ⊢[𝓢]
      (PointwiseComposition.List.disj (φ :: Δ)) ⇒ₗ (PointwiseComposition.List.disj Δ)
    from this⨀(wkProof (by simp) h)
  apply left_Disj_intro
  intro ψ hψ
  rcases show ψ = φ ∨ ψ ∈ Δ by simpa using hψ with (rfl | hψ)
  · apply deductInv
    exact CNC
  · apply right_Disj_intro _ (by simp [hψ])

omit [DecidableEq F] in
lemma neg_left (h : Γ ⟹ Δ ++ [φ]) : ∼φ :: Γ ⟹ Δ := by classical exact neg_left_int (weakening h)
omit [DecidableEq F] in
lemma imply_left_int (hφ : Γ ++ [φ ⇒ₗ ψ] ⟹ Δ ++ [φ]) (hψ : Γ ++ [ψ] ⟹ Δ) : (φ ⇒ₗ ψ) :: Γ ⟹ Δ :=
  by
  classical
  have hφ : (φ ⇒ₗ ψ) :: Γ ⟹ φ :: Δ := weakening hφ
  have hψ : ψ :: Γ ⟹ Δ := weakening hψ
  suffices
    ((φ ⇒ₗ ψ) :: Γ) ⊢[𝓢]
      (PointwiseComposition.List.disj (φ :: Δ)) ⇒ₗ (PointwiseComposition.List.disj Δ)
    from this⨀wkProof (by simp) hφ
  apply left_Disj_intro
  intro χ hχ
  rcases show χ = φ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
  · apply deduct
    have : Γ ⊢[𝓢] ψ ⇒ₗ (PointwiseComposition.List.disj Δ) := deduct hψ
    apply (wkProof (by simp) this)⨀(by_axm₁⨀by_axm₀)
  · apply right_Disj_intro _ (by simp [hχ])

omit [DecidableEq F] in
lemma imply_left (hφ : Γ ⟹ Δ ++ [φ]) (hψ : Γ ++ [ψ] ⟹ Δ) : (φ ⇒ₗ ψ) :: Γ ⟹ Δ := by
  classical exact imply_left_int (weakening hφ) (weakening hψ)
omit [DecidableEq F] in
lemma imply_right_int (h : Γ ++ [φ] ⟹ [ψ]) : Γ ⟹ (φ ⇒ₗ ψ) :: Δ := by
  classical
  have h : φ :: Γ ⟹ [ψ] := weakening h
  have : (φ :: Γ) ⊢[𝓢] ψ := (left_Disj_intro _ <| by simp)⨀h
  exact (right_Disj_intro _ <| by simp)⨀deduct this

omit [DecidableEq F] in
omit [Entailment.Int 𝓢] in
lemma imply_right_cl [Entailment.Cl 𝓢] (h : Γ ++ [φ] ⟹ Δ ++ [ψ]) : Γ ⟹ (φ ⇒ₗ ψ) :: Δ := by
  classical
  have h : φ :: Γ ⟹ ψ :: Δ := weakening h
  have hnφ : Γ ⊢[𝓢] ∼φ ⇒ₗ (PointwiseComposition.List.disj ((φ ⇒ₗ ψ) :: Δ)) :=
    by
    apply right_Disj_intro' ((φ ⇒ₗ ψ) :: Δ) (φ := φ ⇒ₗ ψ) (by simp)
    exact CNC
  have hφ : Γ ⊢[𝓢] φ ⇒ₗ (PointwiseComposition.List.disj ((φ ⇒ₗ ψ) :: Δ)) :=
    by
    apply deduct
    suffices
      (φ :: Γ) ⊢[𝓢]
        (PointwiseComposition.List.disj (ψ :: Δ)) ⇒ₗ
          (PointwiseComposition.List.disj ((φ ⇒ₗ ψ) :: Δ))
      from this⨀h
    apply left_Disj_intro
    intro χ hχ
    rcases show χ = ψ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
    · apply right_Disj_intro' _ (φ := φ ⇒ₗ χ) (by simp)
      exact implyK
    · apply right_Disj_intro
      simp [hχ]
  exact left_A_intro hφ hnφ⨀lem

omit [DecidableEq F] in
omit [Entailment.Int 𝓢] in
lemma iff_right_cl [Entailment.Cl 𝓢] (hr : Γ ++ [φ] ⟹ Δ ++ [ψ]) (hl : Γ ++ [ψ] ⟹ Δ ++ [φ]) :
    Γ ⟹ (φ ⇔ₗ ψ) :: Δ := by
  classical
  apply and_right
  · apply rotate_right_inv
    apply imply_right_cl
    assumption
  · apply rotate_right_inv
    apply imply_right_cl
    assumption

omit [DecidableEq F] in
lemma iff_left (hr : Γ ⟹ Δ ++ [φ, ψ]) (hl : Γ ++ [φ, ψ] ⟹ Δ) : (φ ⇔ₗ ψ) :: Γ ⟹ Δ := by
  classical
  apply and_left
  suffices (φ ⇒ₗ ψ) :: (ψ ⇒ₗ φ) :: Γ ⟹ Δ from weakening this
  apply imply_left
  · apply imply_left
    · exact weakening hr
    · suffices (φ :: Γ) ⟹ φ :: Δ from weakening this
      apply deductInv
      apply right_Disj_intro _ (by simp)
  · suffices (ψ ⇒ₗ φ) :: ψ :: Γ ⟹ Δ from weakening this
    apply imply_left
    · suffices (ψ :: Γ) ⟹ ψ :: Δ from weakening this
      apply deductInv
      apply right_Disj_intro _ (by simp)
    · exact weakening hl

end TwoSided

variable (F)

/-- Data and laws for Sequent in `FFL.Entailment.Tableaux`. -/
structure Tableaux.Sequent where
  /-- The antecedent construction in `FFL.Entailment.Tableaux.Sequent`. -/
  antecedent : List F
  /-- The succedent construction in `FFL.Entailment.Tableaux.Sequent`. -/
  succedent : List F

/-- The Tableaux construction in `FFL.Entailment`. -/
abbrev Tableaux :=
  List (Tableaux.Sequent F)

variable {F} (𝓢)

/-- Data and laws for Valid in `FFL.Entailment.Tableaux`. -/
inductive Tableaux.Valid : Tableaux F → Prop where
  | head {Γ Δ τ} : Γ ⟹ Δ → Valid (⟨Γ, Δ⟩ :: τ)
  | tail {S τ} : Valid τ → Valid (S :: τ)

variable {𝓢}

namespace Tableaux
namespace Valid

variable {T U V : Tableaux F} {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Ξ Ξ₁ Ξ₂ Λ Λ₁ Λ₂ : List F} {φ ψ χ : F}

local notation:0 Γ:45 " ⟶ " Δ:46 => Tableaux.Sequent.mk Γ Δ

omit [DecidableEq F] [Entailment.Int 𝓢]

@[simp]
lemma not_nil : ¬Valid 𝓢 [] := by rintro ⟨⟩

lemma of_mem (H : Γ ⟹ Δ) (h : (Γ ⟶ Δ) ∈ τ) : Valid 𝓢 τ := by
  match τ with
  | [] => simp_all
  |
  (Ξ ⟶ Λ) ::
      τ =>
    rcases show Γ = Ξ ∧ Δ = Λ ∨ (Γ ⟶ Δ) ∈ τ by simpa using h with (⟨rfl, rfl⟩ | h)
    · exact Valid.head H
    · exact (Valid.of_mem H h).tail

lemma of_subset (h : Valid 𝓢 σ) (ss : σ ⊆ τ := by simp) : Valid 𝓢 τ := by
  match σ with
  | [] => simp_all
  | (Γ ⟶ Δ) :: ε =>
    have ss : (Γ ⟶ Δ) ∈ τ ∧ ε ⊆ τ := by simpa using ss
    rcases h with (h | h)
    · exact Valid.of_mem h ss.1
    · exact h.of_subset ss.2

lemma of_single_uppercedent (H : (Γ ⟹ Δ) → (Ξ ⟹ Λ)) (h : Valid 𝓢 ((Γ ⟶ Δ) :: T)) :
    Valid 𝓢 ((Ξ ⟶ Λ) :: T) :=
  by
  have h : Valid 𝓢 ((Γ ⟶ Δ) :: T) := h.of_subset
  rcases h with (h | h)
  · exact Valid.head (H h)
  · exact h.tail

lemma of_double_uppercedent (H : (Γ₁ ⟹ Δ₁) → (Γ₂ ⟹ Δ₂) → (Ξ ⟹ Λ))
    (h₁ : Valid 𝓢 ((Γ₁ ⟶ Δ₁) :: T)) (h₂ : Valid 𝓢 ((Γ₂ ⟶ Δ₂) :: T)) : Valid 𝓢 ((Ξ ⟶ Λ) :: T) :=
  by
  have h₁ : Valid 𝓢 ((Γ₁ ⟶ Δ₁) :: T) := h₁.of_subset
  have h₂ : Valid 𝓢 ((Γ₂ ⟶ Δ₂) :: T) := h₂.of_subset
  rcases h₁ with (h₁ | h₁)
  · rcases h₂ with (h₂ | h₂)
    · exact Valid.head (H h₁ h₂)
    · exact h₂.tail
  · exact h₁.tail

lemma remove : Valid 𝓢 T → Valid 𝓢 ((Γ ⟶ Δ) :: T) :=
  of_subset

variable [DecidableEq F] [Entailment.Int 𝓢]

omit [DecidableEq F] in
lemma to_provable (h : Valid 𝓢 [[] ⟶ [φ]]) : 𝓢 ⊢ φ := by
  classical
  rcases h
  · exact TwoSided.to_provable <| by assumption
  · simp_all

omit [DecidableEq F] in
lemma right_closed (h : φ ∈ Γ) : Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := by
  classical exact head <| TwoSided.right_closed h
omit [DecidableEq F] in
lemma left_closed (h : φ ∈ Δ) : Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) := by
  classical exact head <| TwoSided.left_closed h
omit [DecidableEq F] in
lemma remove_right : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.remove_right
omit [DecidableEq F] in
lemma remove_left : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.remove_left
omit [DecidableEq F] in
lemma rotate_right : Valid 𝓢 ((Γ ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.rotate_right
omit [DecidableEq F] in
lemma rotate_left : Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.rotate_left
omit [DecidableEq F] in
lemma verum_right : Valid 𝓢 ((Γ ⟶ ⊤ :: Δ) :: T) := by
  classical exact Valid.head TwoSided.verum_right
omit [DecidableEq F] in
lemma falsum_left : Valid 𝓢 ((⊥ :: Γ ⟶ Δ) :: T) :=
  Valid.head TwoSided.falsum_left

omit [DecidableEq F] in
lemma falsum_right : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ ⊥ :: Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.falsum_right
omit [DecidableEq F] in
lemma verum_left : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((⊤ :: Γ ⟶ Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.verum_left
omit [DecidableEq F] in
lemma and_right :
    Valid 𝓢 ((Γ ⟶ Δ ++ [φ]) :: T) →
      Valid 𝓢 ((Γ ⟶ Δ ++ [ψ]) :: T) → Valid 𝓢 ((Γ ⟶ φ ⋏ ψ :: Δ) :: T) :=
  by classical exact of_double_uppercedent TwoSided.and_right
omit [DecidableEq F] in
lemma or_left :
    Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) →
      Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋎ ψ :: Γ ⟶ Δ) :: T) :=
  by classical exact of_double_uppercedent TwoSided.or_left
omit [DecidableEq F] in
lemma or_right : Valid 𝓢 ((Γ ⟶ Δ ++ [φ, ψ]) :: T) → Valid 𝓢 ((Γ ⟶ φ ⋎ ψ :: Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.or_right
omit [DecidableEq F] in
lemma and_left : Valid 𝓢 ((Γ ++ [φ, ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋏ ψ :: Γ ⟶ Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.and_left
omit [DecidableEq F] in
lemma neg_right :
    Valid 𝓢 ((Γ ++ [φ] ⟶ []) :: (Γ ⟶ Δ ++ [∼φ]) :: T) → Valid 𝓢 ((Γ ⟶ ∼φ :: Δ) :: T) := by
  classical
  exact
    fun h ↦ by
      rcases h with (h | h)
      · exact Valid.head <| TwoSided.neg_right_int h
      · rcases h with (h | h)
        · apply head
          exact TwoSided.weakening h
        · exact h.tail
omit [DecidableEq F] in
lemma neg_right' :
    Valid 𝓢 ((Γ ++ [φ] ⟶ []) :: (Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ ∼φ :: Δ) :: T) := by
  classical
  exact
    fun h ↦ by
      rcases h with (h | h)
      · exact Valid.head <| TwoSided.neg_right_int h
      · rcases h with (h | h)
        · apply head
          exact TwoSided.weakening h
        · exact h.tail
omit [DecidableEq F] in
lemma neg_left : Valid 𝓢 ((Γ ++ [∼φ] ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((∼φ :: Γ ⟶ Δ) :: T) := by
  classical exact of_single_uppercedent TwoSided.neg_left_int
omit [DecidableEq F] in
lemma imply_right :
    Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ ++ [φ ⇒ₗ ψ]) :: T) → Valid 𝓢 ((Γ ⟶ (φ ⇒ₗ ψ) :: Δ) :: T)
        := by
  classical
  exact
    fun h ↦ by
      have h : Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ ++ [φ ⇒ₗ ψ]) :: T) := h.of_subset
      rcases h with (h | h)
      · exact Valid.head <| TwoSided.imply_right_int h
      · rcases h with (h | h)
        · apply head
          exact TwoSided.weakening h
        · exact h.tail

omit [DecidableEq F] in
lemma imply_right' :
    Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ) :: T) → Valid 𝓢 ((Γ ⟶ (φ ⇒ₗ ψ) :: Δ) :: T) := by
  classical
  exact
    fun h ↦ by
      have h : Valid 𝓢 ((Γ ++ [φ] ⟶ [ψ]) :: (Γ ⟶ Δ) :: T) := h.of_subset
      rcases h with (h | h)
      · exact Valid.head <| TwoSided.imply_right_int h
      · rcases h with (h | h)
        · apply head
          exact TwoSided.weakening h
        · exact h.tail
omit [DecidableEq F] in
lemma imply_left :
    Valid 𝓢 ((Γ ++ [φ ⇒ₗ ψ] ⟶ Δ ++ [φ]) :: T) →
      Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 (((φ ⇒ₗ ψ) :: Γ ⟶ Δ) :: T) :=
  by classical exact of_double_uppercedent TwoSided.imply_left_int
end Valid
end Tableaux

end Entailment
end FFL

end

end PointwiseComposition

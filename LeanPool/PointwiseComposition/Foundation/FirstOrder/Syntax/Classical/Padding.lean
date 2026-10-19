/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Tarski.Basic
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.LK.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace FirstOrder

variable {L : Language} {ξ : Type*}

namespace Semiformula

/-- The padding construction in `FFL.FirstOrder.Semiformula`. -/
def padding (φ : Semiformula L ξ n) (k : ℕ) :=
  φ ⋏ (PointwiseComposition.List.conj (List.replicate k ⊤))

/-- The get Padding Aux construction in `FFL.FirstOrder.Semiformula`. -/
def getPaddingAux : Semiformula L ξ n → Option ℕ
  | ⊤ => some 0
  | ⊤ ⋏ φ => φ.getPaddingAux.map fun x ↦ x + 1
  | _ => none

/-- The get Padding construction in `FFL.FirstOrder.Semiformula`. -/
def getPadding : Semiformula L ξ n → Option ℕ
  | _ ⋏ φ => φ.getPaddingAux
  | _ => none

/-- The get Padding Formula construction in `FFL.FirstOrder.Semiformula`. -/
def getPaddingFormula : Semiformula L ξ n → Option (Semiformula L ξ n)
  | φ ⋏ _ => some φ
  | _ => none

@[simp]
lemma getPadding_padding (φ : Semiformula L ξ n) : (φ.padding k).getPadding = some k :=
  by
  suffices
    (PointwiseComposition.List.conj (List.replicate k (⊤ : Semiformula L ξ n))).getPaddingAux =
      some k
    by simpa [getPadding, padding]
  induction k <;> simp [List.replicate_succ, getPaddingAux, *]

@[simp]
lemma getPaddingFormula_padding (φ : Semiformula L ξ n) :
    (φ.padding k).getPaddingFormula = some φ := by simp [padding, getPaddingFormula]

@[simp]
lemma padding_injective_iff {φ ψ : Semiformula L ξ n} :
    φ.padding k = ψ.padding m ↔ φ = ψ ∧ k = m :=
  ⟨fun h ↦
    ⟨by simpa using congr_arg getPaddingFormula h, by simpa using congr_arg getPadding h⟩, by
    rintro ⟨rfl, rfl⟩; rfl⟩

@[simp]
lemma rew_padding (ω : Rew L ξ n ξ' n') (φ : Semiformula L ξ n) :
    ω ▹ φ.padding k = (ω ▹ φ).padding k :=
  by
  simp [padding]
  induction k <;> simp [List.replicate_succ, *]

end Semiformula

open Entailment

/-- The padding Iff construction in `FFL.FirstOrder.Entailment`. -/
def Entailment.paddingIff [L.DecidableEq] [DecidableEq ξ] [Entailment S (Formula L ξ)] {𝓢 : S}
    [Entailment.Minimal 𝓢] (φ k) : 𝓢 ⊢! φ.padding k ⇔ₗ φ :=
  by
  apply EProofIntro
  · apply and₁Proof
  · apply rightKProofIntro
    · apply CProofId
    · apply dhypProof
      apply ConjProofIntro
      intro φ hφ
      have : k ≠ 0 ∧ φ = ⊤ := by simpa using hφ;
      exact this.2 ▸ HasAxiomVerum.verumProof

@[simp]
theorem Entailment.padding_iff [L.DecidableEq] [Entailment S (Formula L ξ)] {𝓢 : S}
    [Entailment.Minimal 𝓢] (φ k) : 𝓢 ⊢ φ.padding k ⇔ₗ φ := by classical exact ⟨paddingIff φ k⟩

end FirstOrder
end FFL

end

end PointwiseComposition

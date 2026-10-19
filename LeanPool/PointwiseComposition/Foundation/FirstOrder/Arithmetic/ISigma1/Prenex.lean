/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Prenex

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Prenex normal form theorem over $\mathsf{I\Sigma_1}$

Every `Hierarchy Σ 1` formula is `𝐈Σ₁`-provably equivalent to a formula of the form `∃¹ θ`
with `θ` in `Hierarchy Σ 0`, and dually for `Hierarchy Π 1` and `∀¹ θ`.
-/

@[expose] public section

open FFL

open FFL.FirstOrder

namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace ISigma1

variable {n : ℕ} {φ : ArithmeticSemisentence n} {σ : ArithmeticSentence}

lemma hasPrenex (h : Hierarchy Σ 1 φ) : ∃ φ' : Prenex Σ 1 Empty n, 𝐈Σ₁ ⊢ ∀¹* (φ ⇔ₗ φ'.val) :=
  exists_prenex_of_hierarchy 𝐈Σ₁ h

lemma exists_matrix_provable (h : Hierarchy Σ 1 φ) :
    ∃ θ : Σ₀.Semisentence (n + 1), 𝐈Σ₁ ⊢ ∀¹* (φ ⇔ₗ ∃¹ θ.val) := by
  obtain ⟨φ', hφ'⟩ := hasPrenex h; exact ⟨φ'.sigmaInv.matrix, Prenex.provable_iff_sigmaInv hφ'⟩

lemma exists_matrix_provable_pi (h : Hierarchy Π 1 φ) :
    ∃ θ : Σ₀.Semisentence (n + 1), 𝐈Σ₁ ⊢ ∀¹* (φ ⇔ₗ ∀¹ θ.val) :=
  by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy 𝐈Σ₁ h
  exact ⟨φ'.piInv.matrix, Prenex.provable_iff_piInv hφ'⟩

lemma exists_matrix_provable_of_sentence (h : Hierarchy Σ 1 σ) :
    ∃ θ : Σ₀.Semisentence 1, 𝐈Σ₁ ⊢ σ ⇔ₗ ∃¹ θ.val :=
  exists_matrix_provable h

end ISigma1
end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition

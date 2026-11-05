/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D1}$ and soundness of internal provability.
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace Bootstrapping

open FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁]

open _root_.Classical in
lemma derivable_quote {Γ : Finset (Proposition L)} (d : T ⟹₂Γ) : Derivable T (⌜Γ⌝ : V) :=
  ⟨⌜d⌝, by
    simpa [Semiformula.quote_def] using! (⌜d⌝ : Theory.internalize V T ⊢!ᵈᵉʳ ⌜Γ⌝).derivationOf⟩

/-- Hilbert–Bernays provability condition D1 -/
theorem internalize_provability {φ} : T ⊢ φ → Provable T (⌜φ⌝ : V) := fun h ↦ by
  classical
  simpa using! derivable_quote (V := V) (provable_iff_derivable2.mp h).some

theorem internal_provable_of_outer_provable {φ} : T ⊢ φ → T.internalize V ⊢ ⌜φ⌝ := fun h ↦ by
  classical
  simpa [TProvable.iff_provable] using! internalize_provability (V := V) h

@[simp]
lemma Provable.complete {φ : Sentence L} : T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ :=
  by
  classical
  exact ⟨by simpa [TProvable.iff_provable] using! Provable.sound,
    internal_provable_of_outer_provable⟩

@[simp]
lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : Sentence L} :
    Provable T (⌜φ⌝ : ℕ) ↔ T ⊢ φ := by
  classical
  simpa [TProvable.iff_provable] using! Provable.complete

end Bootstrapping
end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition

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
# Hilbert-Bernays-Löb derivability condition $\mathbf{D2}$
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace Bootstrapping

open FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁]

/-- Hilbert–Bernays provability condition D2 -/
theorem modus_ponens {φ ψ : Proposition L} (hφψ : Provable T (⌜φ ⇒ₗ ψ⌝ : V))
    (hφ : Provable T (⌜φ⌝ : V)) : Provable T (⌜ψ⌝ : V) :=
  by
  apply (tprovable_tquote_iff_provable_quote (L := L)).mp
  have hφψ : Theory.internalize V T ⊢ ⌜φ⌝ ⇒ₗ ⌜ψ⌝ := by
    simpa using (tprovable_tquote_iff_provable_quote (L := L)).mpr hφψ
  have hφ : Theory.internalize V T ⊢ ⌜φ⌝ :=
    (tprovable_tquote_iff_provable_quote (L := L)).mpr hφ
  exact hφψ⨀hφ

theorem modus_ponens_sentence {σ τ : Sentence L} (hστ : Provable T (⌜σ ⇒ₗ τ⌝ : V))
    (hσ : Provable T (⌜σ⌝ : V)) : Provable T (⌜τ⌝ : V) :=
  by
  apply (tprovable_tquote_iff_provable_quote (L := L)).mp
  have hστ : Theory.internalize V T ⊢ ⌜σ⌝ ⇒ₗ ⌜τ⌝ := by
    simpa using! (tprovable_tquote_iff_provable_quote (L := L)).mpr hστ
  have hσ : Theory.internalize V T ⊢ ⌜σ⌝ :=
    (tprovable_tquote_iff_provable_quote (L := L)).mpr hσ
  exact hστ⨀hσ

end Bootstrapping
end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition

/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Basic.Misc

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace FirstOrder

namespace Tarski
namespace Structure

/-- Data and laws for Monotone in `FFL.FirstOrder.Tarski.Structure`. -/
class Monotone (L : Language) (M : Type*) [LE M] [Tarski.Structure L M] where
  monotone :
    ∀ {k} (f : L.Func k) (v₁ v₂ : Fin k → M),
      (∀ i, v₁ i ≤ v₂ i) → Tarski.Structure.func f v₁ ≤ Tarski.Structure.func f v₂

namespace Monotone

variable {L : Language} {M : Type*} [LE M] [Tarski.Structure L M] [Monotone L M]

lemma term_monotone (t : Semiterm L ξ n) {fv₁ fv₂ : Fin n → M} {bv₁ bv₂ : ξ → M}
    (he : ∀ i, fv₁ i ≤ fv₂ i) (hε : ∀ i, bv₁ i ≤ bv₂ i) : t.val fv₁ bv₁ ≤ t.val fv₂ bv₂ := by
  induction t <;> simp [*, Semiterm.val_func, Monotone.monotone]

end Monotone

end Structure
end Tarski

end FirstOrder

end FFL

end

end PointwiseComposition

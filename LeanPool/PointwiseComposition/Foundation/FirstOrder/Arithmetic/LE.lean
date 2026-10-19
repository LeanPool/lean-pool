/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.LK.Completeness

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL

namespace FirstOrder

variable {L : Language.{u}} [Semiformula.Operator.Eq L] [Semiformula.Operator.LT L]

open Semiformula

/-- The le construction in `FFL.FirstOrder.LT`. -/
def LT.le : Operator L 2 :=
  Semiformula.Operator.Eq.eq.or Semiformula.Operator.LT.lt

lemma le_eq (t₁ t₂ : Semiterm L μ n) :
    LT.le.operator ![t₁, t₂] = (“!!t₁ = !!t₂ ∨ !!t₁ < !!t₂”) := by
  simp [Operator.operator, Operator.or, LT.le, ← TransitiveRewriting.comp_app]

namespace Order

open _root_.Order

variable {T : Theory L} [𝐄𝐐 L ≼ T]

omit [𝐄𝐐 L ≼ T] in
theorem leIffEqOrLt : T ⊢ (“∀ x y, x ≤ y ↔ x = y ∨ x < y”) :=
  Theory.Proof.small_complete <|
    consequence_iff.mpr fun _ ↦ by simp [models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT]

lemma complete (φ : Sentence L)
    (H :
      ∀ (M : Type (max u w)) [Nonempty M] [LT M] [Tarski.Structure L M]
        [Tarski.Structure.Eq L M] [Tarski.Structure.LT L M] [M↓[L] ⊧* T], M↓[L] ⊧ φ) :
    T ⊢ φ :=
  Theory.Proof.complete <|
    consequence_iff_eq.mpr fun M _ _ _ hT ↦
      letI : (Tarski.Structure.Model L M)↓[L] ⊧* T :=
        Tarski.Structure.ElementaryEquiv.modelsTheory.mp hT
      Tarski.Structure.ElementaryEquiv.models.mpr (H (Tarski.Structure.Model L M))

end Order

end FirstOrder

end FFL

end

end PointwiseComposition

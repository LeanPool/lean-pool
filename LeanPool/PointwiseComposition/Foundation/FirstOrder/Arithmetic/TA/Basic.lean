/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace FirstOrder
namespace Arithmetic

/-- The 𝐓𝐀 construction in `𝐓𝐀`. -/
abbrev FirstOrderTrueArith : ArithmeticTheory :=
  Tarski.Structure.theory ℒₒᵣ ℕ

/-- The «term𝐓𝐀» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "𝐓𝐀" => FirstOrderTrueArith

namespace TA

instance : ℕ↓[ℒₒᵣ] ⊧* 𝐓𝐀 :=
  models_theory_iff.mpr fun {φ} ↦ by simp

lemma provable_iff {φ : ArithmeticSentence} : 𝐓𝐀 ⊢ φ ↔ ℕ↓[ℒₒᵣ] ⊧ φ :=
  ⟨fun h ↦ consequence_iff'.mp (Theory.Proof.sound h) ℕ, fun h ↦ Entailment.by_axm h⟩

instance (T : ArithmeticTheory) [ℕ↓[ℒₒᵣ] ⊧* T] : T ≼ 𝐓𝐀 :=
  ⟨by
    rintro φ h
    have : ℕ↓[ℒₒᵣ] ⊧ φ := consequence_iff'.mp (Theory.Proof.sound h) ℕ
    exact provable_iff.mpr this⟩

end TA

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition

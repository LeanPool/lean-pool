/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.Consistency
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.RosserProvability
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic

open FFL.Entailment ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁] [𝐈Σ₁ ≼ T]

/-- Gödel's second incompleteness theorem -/
theorem consistent_unprovable [Consistent T] : T ⊬ T.consistent.val :=
  ProvabilityAbstraction.con_unprovable (𝔅 := T.standardProvability)

/-- Gödel's second incompleteness theorem for r.e. theories -/
theorem craig_consistent_unprovable_of_RE (T : ArithmeticTheory) [T.RE] [𝐈Σ₁ ≼ T]
    [Consistent T] : T ⊬ T.craig.consistent.val := fun h ↦
  consistent_unprovable T.craig (WeakerThan.pbl h)

theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T Σ 1] :
    T ⊬ ∼T.consistent.val :=
  ProvabilityAbstraction.con_unrefutable (𝔅 := T.standardProvability)

/-- The consistency statement is independent. -/
theorem inconsistent_independent [ArithmeticTheory.SoundOnHierarchy T Σ 1] :
    Independent T T.consistent.val :=
  ProvabilityAbstraction.con_independent (𝔅 := T.standardProvability)

instance [Consistent T] : T ≺ T ∪ T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := T.consistent) (consistent_unprovable T)
    (Entailment.by_axm (by simp))

instance [ArithmeticTheory.SoundOnHierarchy T Σ 1] : T ≺ T ∪ T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼T.consistent) (inconsistent_unprovable T)
    (Entailment.by_axm (by simp))

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition

/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexAuxiliarySeparation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexStageHierarchyResources

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators

namespace AuxiliarySeparation

variable {X Y Z Label : Type*} [Fintype Label] [DecidableEq Label]

theorem directSum_rankAtMost (T : Tensor ℂ X Y Z)
    (readX : X → Label) (readY : Y → Label) {R : ℕ}
    (hT : Tensor.RankAtMost T R)
    (readable : ∀ x y z, T x y z ≠ 0 → readX x = readY y) :
    Tensor.RankAtMost (Tensor.dependentDirectSum (fun label =>
      Tensor.product (labelFiberTensor readX readY T label)
        (Tensor.dotPairing (Fin (Fintype.card Label)))))
      (R * Separation.gridGroupOrder (Fintype.card Label)) :=
  auxiliary_separation_directSum_rankAtMost T readX readY hT readable

theorem directSum_borderRankAtMost
    (T : Tensor ℂ X Y Z) (readX : X → Label) (readY : Y → Label) {R : ℕ}
    (hT : Tensor.BorderRankAtMost T R)
    (readable : ∀ x y z, T x y z ≠ 0 → readX x = readY y) :
    Tensor.BorderRankAtMost (Tensor.dependentDirectSum (fun label =>
      Tensor.product (labelFiberTensor readX readY T label)
        (Tensor.dotPairing (Fin (Fintype.card Label)))))
      (R * Separation.gridGroupOrder (Fintype.card Label)) :=
  auxiliary_separation_directSum_borderRankAtMost T readX readY hT readable

theorem logarithmic_cost :
    Tendsto (fun K : ℕ => Real.log (Separation.gridGroupOrder K : ℝ) /
      Real.log (K : ℝ)) atTop (𝓝 1) :=
  auxiliary_separation_logarithmic_cost

theorem cost_minus_population_tendsto_zero {population : ℕ → ℕ} {rate : ℝ}
    (positive : ∀ n, 0 < population n) (rate_nonneg : 0 ≤ rate)
    (population_rate : Tendsto
      (fun n => Real.log (population n : ℝ) / (n : ℝ)) atTop (𝓝 rate)) :
    Tendsto (fun n =>
      (Real.log (LabelHierarchySeparation.poolAuxiliaryCost (population n) : ℝ) -
        Real.log (population n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
    positive rate_nonneg population_rate).sub population_rate
  simpa only [sub_self, sub_div] using h

end AuxiliarySeparation
end MatrixMultiplication

end

end MatrixMultiplicationAllFields

/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Entropy.ComplexSeparationAsymptotics
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSeparatedTensorDecomposition

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

instance auxiliarySeparation_modulus_neZero (K : ℕ) :
    NeZero (4 * Separation.gridWidth K) :=
  ⟨Nat.mul_ne_zero (by decide)
    (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two K)))⟩

section AuxiliarySeparation

variable {X Y Z S : Type*} [Fintype S] [DecidableEq S]

theorem auxiliary_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin (Fintype.card S)) lx T ∈ Tensor.restrictionOrbit
      (Tensor.product T (groupTensor (Separation.AuxiliaryGroup
        (Separation.gridDimension (Fintype.card S))
        (Separation.gridWidth (Fintype.card S))))) := by
  exact finite_grid_separation_mem_restrictionOrbit T lx ly
    (Separation.grid_population_bound (Fintype.card S))
    (Separation.grid_population_bound (Fintype.card S)) hlabels

theorem auxiliary_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (separatedTensor (U := Fin (Fintype.card S)) lx T)
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact finite_grid_separation_rankAtMost T lx ly
    (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two (Fintype.card S)))
    (Separation.grid_population_bound (Fintype.card S))
    (Separation.grid_population_bound (Fintype.card S)) hT hlabels

theorem auxiliary_separation_borderRankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost (separatedTensor (U := Fin (Fintype.card S)) lx T)
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact finite_grid_separation_borderRankAtMost T lx ly
    (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two (Fintype.card S)))
    (Separation.grid_population_bound (Fintype.card S))
    (Separation.grid_population_bound (Fintype.card S)) hT hlabels

theorem auxiliary_separation_directSum_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s)
        (Tensor.dotPairing (Fin (Fintype.card S)))))
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact separatedTensor_fiber_directSum_rankAtMost T lx ly hlabels
    (auxiliary_separation_rankAtMost T lx ly hT hlabels)

theorem auxiliary_separation_directSum_borderRankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s)
        (Tensor.dotPairing (Fin (Fintype.card S)))))
      (r * Separation.gridGroupOrder (Fintype.card S)) := by
  exact separatedTensor_fiber_directSum_borderRankAtMost T lx ly hlabels
    (auxiliary_separation_borderRankAtMost T lx ly hT hlabels)

end AuxiliarySeparation

theorem auxiliary_separation_logarithmic_cost :
    Filter.Tendsto
      (fun K : ℕ => Real.log (Separation.gridGroupOrder K : ℝ) / Real.log (K : ℝ))
      Filter.atTop (nhds 1) :=
  Separation.tendsto_log_gridGroupOrder_div_log_population

end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields

/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8PositiveGridKernel
public import LeanPool.C145.C145GraphSpectralRealization

/-! Application checks for the actual response and norm definitions.
The first is a counterexample to dropping positive-grid hypotheses: totalized
division hides a nonzero tensor at a pole. The second distinguishes the source
Frobenius norm from the ordinary function-space maximum norm. -/

@[expose] public section

namespace C145.PaperChecks
open C145.H2 C145DRE8
open scoped BigOperators

/-- The one-mode tensor with its only entry equal to one. -/
def unitTensor : Tensor 1 := fun _ _ _ => 1
/-- The unit rate in the one-mode domain check. -/
def unitRates : Fin 1 → ℝ := fun _ => 1
/-- The unit overlap in the one-mode domain check. -/
def unitOverlap : Fin 1 → ℝ := fun _ => 1

theorem response_at_pole : H unitRates unitTensor (-1) 1 = 0 := by
  norm_num [H, unitRates, unitTensor, Fin.sum_univ_one]

theorem response_at_positive_point : H unitRates unitTensor 1 1 = 1 / 12 := by
  norm_num [H, unitRates, unitTensor, Fin.sum_univ_one]

theorem nonpositive_grid_can_hide_nonzero_response :
    positiveGridMap unitOverlap unitRates
      (fun _ => -1) (fun _ => 1) (fromTensor unitTensor) = 0 ∧
    fromTensor unitTensor ∉ actualPositiveKernel unitOverlap unitRates := by
  constructor
  · ext p
    change H unitRates (weightedTensor unitOverlap unitTensor) (-1) 1 = 0
    simp [weightedTensor, H, unitRates, unitOverlap, unitTensor]
  · intro hz
    have h := hz 1 1 (by norm_num) (by norm_num)
    norm_num [responseMap_apply, weightedTensor, toTensor_fromTensor,
      H, unitRates, unitOverlap, unitTensor, Fin.sum_univ_one] at h

theorem constant_tensor_frobenius_sq :
    ‖fromTensor (fun _ _ _ : Fin 2 => (1 : ℝ))‖ ^ 2 = 8 := by
  rw [norm_fromTensor_sq]
  norm_num [tensorSq, Fin.sum_univ_two]

theorem constant_tensor_function_norm :
    ‖(fun _ _ _ : Fin 2 => (1 : ℝ))‖ = 1 := by
  change ‖(1 : Fin 2 → Fin 2 → Fin 2 → ℝ)‖ = 1
  exact norm_one

/-- A constant port on three vertices cannot be cyclic for ANY graph
Laplacian. Thus the graph theorem's cyclicity condition rejects a genuine
unobservable-mode boundary, rather than accepting the zero-overlap case. -/
theorem constant_port_not_cyclic
    (μ : ℝ) (W : Matrix (Fin 3) (Fin 3) ℝ) :
    ¬ C145.CyclicSpectral.KrylovCyclic
      (C145.GraphSpectralRealization.generator μ W) (fun _ => 1) := by
  open Matrix C145.WeightedGraph C145.GraphSpectralRealization in
  intro hcyc
  let A := generator μ W
  let b : Fin 3 → ℝ := fun _ => 1
  have he : A *ᵥ b = (-μ) • b := by
    change (-μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - laplacian W) *ᵥ b = _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      show laplacian W *ᵥ b = 0 from laplacian_const W 1]
    simp
  have hk : ∀ k : ℕ, A ^ k *ᵥ b = (-μ) ^ k • b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, he, smul_smul]
        congr 1
  have hz : (![1,-1,0] : Fin 3 → ℝ) = 0 :=
    C145.CyclicSpectral.cyclic_annihilator A b ![1,-1,0] hcyc (by
      intro k
      rw [hk]
      norm_num [dotProduct, b, Fin.sum_univ_succ])
  have hv := congrFun hz 0
  norm_num at hv

end C145.PaperChecks

end

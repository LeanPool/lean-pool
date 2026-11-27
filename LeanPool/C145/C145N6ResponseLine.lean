/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145N6TraceLine
public import LeanPool.C145.C145N6LineExclusion

/-!
# Reduction of compatible six-vertex tensors to an affine line.
-/

@[expose] public section
noncomputable section
namespace C145N6
open C145.H2 C145.ThreePlane
open scoped BigOperators

theorem saved_residue_entries (t : ℝ) (i j k : Fin 5) :
    Res rates (fourForm (fun h => t * savedQ h)) i j k =
      t * C145N6Literal.directionTensor i.succ j.succ k.succ := by
  rw [res_entry, eval_fourForm, xi_negative_node_factors]
  simp only [rates_di]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [rates, savedQ, C145N6Literal.directionTensor] <;> ring

theorem ground_saved_residue (t : ℝ) :
    groundZero (Res rates (fourForm (fun h => t * savedQ h))) =
      fun i j k => t * C145N6Literal.directionTensor i j k := by
  funext i j k
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [groundZero_ground_first]
    fin_cases j <;> fin_cases k <;> norm_num [C145N6Literal.directionTensor]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [groundZero_ground_second]
      fin_cases i <;> fin_cases k <;> norm_num [C145N6Literal.directionTensor]
    · refine Fin.cases ?_ (fun k => ?_) k
      · rw [groundZero_ground_output]
        fin_cases i <;> fin_cases j <;> norm_num [C145N6Literal.directionTensor]
      · exact saved_residue_entries t i j k

theorem admissible_trace_residue_line (R : Poly) (hs : SymPoly R)
    (ha : QAdmissible 5 R) (a : Fin 6 → ℝ)
    (hw : ∀ i, a i ^ 2 = C145N6Literal.overlapSquare i)
    (ht : ResidualTraceFree a (Res rates R)) :
    ∃ t : ℝ, groundZero (Res rates R) = fun i j k => t * C145N6Literal.directionTensor i j k := by
  obtain ⟨c,rfl⟩ := admissible_five_four R hs ha
  have hc : ∀ i, literalTrace c i = 0 := by
    intro i
    simpa only [literalTrace, ResidualTraceFree, residualCountingTrace, hw] using ht i
  have he := trace_kernel_saved_line c hc
  refine ⟨c 3 / savedQ 3, ?_⟩
  conv_lhs => rw [he]
  exact ground_saved_residue _

theorem rates_injective : Function.Injective rates := by
  intro i j h; fin_cases i <;> fin_cases j <;> norm_num [rates] at *
theorem rates_positive : ∀ i, 0 < rates i := by
  intro i; fin_cases i <;> norm_num [rates]

/-- Actual response-to-line consequence for two physical frames with the saved weights.
No existence or construction of a frame realizing the saved base tensor is asserted. -/
theorem physical_response_saved_line
    (μ : ℝ) (Q0 Q1 : Fin 6 → Fin 6 → ℝ) (a : Fin 6 → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (ha : ∀ i, a i ≠ 0)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c)
    (hw : ∀ i, a i ^ 2 = C145N6Literal.overlapSquare i)
    (hH : SamePositive (fullRates μ rates) (C145PhysicalFrame.T Q0 a) (C145PhysicalFrame.T Q1 a)) :
    ∃ t : ℝ, C145PhysicalFrame.T Q1 a - C145PhysicalFrame.T Q0 a =
      fun i j k => t * C145N6Literal.directionTensor i j k := by
  obtain ⟨R,hR,_⟩ := (physical_pair_H2_counting_trace_residue μ rates rates_injective
    rates_positive Q0 Q1 a c hQ0 hQ1 ha hG0 hG1).mp hH
  obtain ⟨t,ht⟩ := admissible_trace_residue_line R hR.1 hR.2.1 a hw hR.2.2.2.1
  exact ⟨t,hR.2.2.1.trans ht⟩

/-- Conditional physical uniqueness at the saved tensor, with realization kept explicit. -/
theorem physical_saved_base_unique
    (μ : ℝ) (Q0 Q1 : Fin 6 → Fin 6 → ℝ) (a : Fin 6 → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (ha : ∀ i, a i ≠ 0)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c)
    (hw : ∀ i, a i ^ 2 = C145N6Literal.overlapSquare i)
    (hbase : C145PhysicalFrame.T Q0 a = C145N6Literal.baseTensor)
    (hH : SamePositive (fullRates μ rates) (C145PhysicalFrame.T Q0 a) (C145PhysicalFrame.T Q1 a)) :
    C145PhysicalFrame.T Q1 a = C145N6Literal.baseTensor := by
  obtain ⟨t,ht⟩ := physical_response_saved_line μ Q0 Q1 a c hQ0 hQ1 ha hG0 hG1 hw hH
  have hline : C145PhysicalFrame.T Q1 a = C145N6Literal.tensorLine t := by
    funext i j k
    have he := congrFun (congrFun (congrFun ht i) j) k
    rw [hbase] at he
    change C145PhysicalFrame.T Q1 a i j k - C145N6Literal.baseTensor i j k =
      t * C145N6Literal.directionTensor i j k at he
    dsimp [C145N6Literal.tensorLine]
    linarith
  have hassoc : ∀ i j k l, C145N6Literal.assocResidual (C145N6Literal.tensorLine t) i j k l = 0 :=
    by
    intro i j k l
    have hh := C145PhysicalFrame.modal_associativity Q1 a hQ1 ha i j k l
    simpa only [C145PhysicalFrame.Assoc, hw, hline, C145N6Literal.assocResidual] using hh
  exact hline.trans (C145N6Literal.associative_literal_line_unique t hassoc).2
end C145N6

end

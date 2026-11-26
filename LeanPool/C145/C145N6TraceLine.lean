/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145N6Squarefree
public import LeanPool.C145.C145PhysicalTraceResidue
public import LeanPool.C145.C145N6LiteralRows

/-!
# Trace constraints on the six-vertex affine tensor line.
-/

@[expose] public section
namespace C145N6
open MvPolynomial C145.H2 C145.ThreePlane
open scoped BigOperators
noncomputable section
/-- The five exact non-ground rates of the six-vertex source. -/
def rates : Fin 5 → ℝ := ![20,21,22,23,24]
/-- The four rational-basis coefficients of the saved polynomial direction. -/
def savedQ : Fin 4 → ℝ :=
  ![325764900351929037312, 14674136896174112640, 660275376511893120, 29677554006883200]
theorem admissible_five_four (R : Poly) (hs : SymPoly R) (ha : QAdmissible 5 R) : ∃ c, R =
  fourForm c := by
  apply symmetric_squarefree_four R _ hs
  rcases ha with rfl | ⟨_,h⟩
  · simp
  · simpa using h

theorem univ_five : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide

theorem rates_di (i : Fin 5) : di rates i = (![24,-6,4,-6,24] : Fin 5 → ℝ) i := by
  fin_cases i
  · have he : (Finset.univ : Finset (Fin 5)).erase 0 = {1,2,3,4} := by decide
    norm_num [di, he, rates]
  · have he : (Finset.univ : Finset (Fin 5)).erase 1 = {0,2,3,4} := by decide
    norm_num [di, he, rates]
  · have he : (Finset.univ : Finset (Fin 5)).erase 2 = {0,1,3,4} := by decide
    norm_num [di, he, rates]
  · have he : (Finset.univ : Finset (Fin 5)).erase 3 = {0,1,2,4} := by decide
    norm_num [di, he, rates]
  · have he : (Finset.univ : Finset (Fin 5)).erase 4 = {0,1,2,3} := by decide
    norm_num [di, he, rates]

theorem eval_exponent (v : Fin 3 → ℝ) (a b c : ℕ) (r : ℝ) :
    eval v (monomial (exponent a b c) r) = r * v 0 ^ a * v 1 ^ b * v 2 ^ c := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero (v i))]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  simp only [exponent_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  change r * (v 0 ^ a * (v 1 ^ b * v 2 ^ c)) = _
  ring

theorem eval_fourForm (c : Fin 4 → ℝ) (v : Fin 3 → ℝ) :
    eval v (fourForm c) = c 0 + c 1 * (v 0 + v 1 + v 2)+
      c 2 * (v 0 * v 1 + v 0 * v 2 + v 1 * v 2) + c 3 * v 0 * v 1 * v 2 := by
  simp only [fourForm, map_add, eval_exponent, pow_zero, pow_one]
  ring

/-- The modal trace obtained by dividing by the literal squared overlaps before summing. -/
def literalTrace (c : Fin 4 → ℝ) (i : Fin 5) : ℝ :=
  ∑ j, Res rates (fourForm c) i j j / C145N6Literal.overlapSquare j.succ

theorem literalTrace_0 (c : Fin 4 → ℝ) : literalTrace c 0 = ((-2161682433875 : ℝ) / 4772455254) *
  c 0 + ((2590386854600 : ℝ) / 88378801) * c 1 + ((-502389654429350 : ℝ) / 795409209) * c 2 +
  ((10813930971581000 : ℝ) / 2386227627) * c 3 := by
  simp only [literalTrace, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    res_entry, eval_fourForm, xi_negative_node_factors, rates_di]
  norm_num [rates, di, C145N6Literal.overlapSquare, Fin.prod_univ_succ, univ_five,
    Finset.erase_insert]; ring

theorem literalTrace_1 (c : Fin 4 → ℝ) : literalTrace c 1 = ((41477827055 : ℝ) / 21643788) * c 0 +
  ((-5451258232891 : ℝ) / 43287576) * c 1 + ((119398730088541 : ℝ) / 43287576) * c 2 +
  ((-72635063655595 : ℝ) / 3607298) * c 3 := by
  simp only [literalTrace, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    res_entry, eval_fourForm, xi_negative_node_factors, rates_di]
  norm_num [rates, di, C145N6Literal.overlapSquare, Fin.prod_univ_succ, univ_five,
    Finset.erase_insert]; ring

theorem literalTrace_2 (c : Fin 4 → ℝ) : literalTrace c 2 = ((-3204241771555 : ℝ) / 1060545612) *
  c 0 + ((53444263864673 : ℝ) / 265136403) * c 1 + ((-1188931306461074 : ℝ) / 265136403) * c 2 +
  ((8819156627521306 : ℝ) / 265136403) * c 3 := by
  simp only [literalTrace, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    res_entry, eval_fourForm, xi_negative_node_factors, rates_di]
  norm_num [rates, di, C145N6Literal.overlapSquare, Fin.prod_univ_succ, univ_five,
    Finset.erase_insert]; ring


theorem trace_kernel_saved_line (c : Fin 4 → ℝ)
    (h : ∀ i, literalTrace c i = 0) : c = fun j => (c 3 / savedQ 3) * savedQ j := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [literalTrace_0] at h0
  rw [literalTrace_1] at h1
  rw [literalTrace_2] at h2
  funext j
  fin_cases j
  · norm_num [savedQ]
    linear_combination (-1012140890719171805529 / 2189964760013133125 : ℝ) * h0 +
      (-19131961758132556272 / 87598590400525325 : ℝ) * h1 + (-733947426801789698946 /
      10599429438463564325 : ℝ) * h2
  · norm_num [savedQ]
    linear_combination (-24154892621559002709 / 1751971808010506500 : ℝ) * h0 + (-1130255387454988
      / 173462555248565 : ℝ) * h1 + (-8759224410433715323 / 4239771775385425730 : ℝ) * h2
  · norm_num [savedQ]
    linear_combination (-7846778375163 / 25446583218500 : ℝ) * h0 + (-37086758476 / 254465832185 :
      ℝ) * h1 + (-2845910411141 / 61580731388770 : ℝ) * h2
  · norm_num [savedQ]
end
end C145N6

end

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebDense.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCenter
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebDensityGenerator
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceWeightedEllipticLiouville
/-!
# Correspondence Brascamp Lieb dense

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_core_orthogonal_constants`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] [DecidableEq ι] in
theorem correspondenceBrascampLieb_weighted_generator_eq
    (W f : E → ℝ) (b : OrthonormalBasis ι ℝ E) (hW : ContDiff ℝ 1 W) :
    correspondenceWeightedEllipticGenerator b (bakryEmeryGibbsWeight W) f =
      bakryEmeryGibbsGenerator W b f := by
  classical
  funext x
  rw [correspondenceBrascampLieb_density_generator W f b hW]
  unfold correspondenceWeightedEllipticGenerator bakryEmeryGibbsDirectional
  exact Finset.sum_add_distrib

omit [CompleteSpace E] [DecidableEq ι] in
omit [DecidableEq ι] in
/-- Genuine elliptic range-density identification for the concrete Gibbs
measure. Its analytic completion inputs are all proved internally. -/
theorem correspondenceBrascampLieb_core_orthogonal_constants
    (W : E → ℝ) (b : OrthonormalBasis ι ℝ E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)] :
    (correspondenceBrascampLiebCoreRange W b hW)ᗮ =
      (ℝ ∙ correspondenceBrascampLiebOneL2 W) := by
  classical
  apply le_antisymm
  · intro u hu
    have hAnn : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ x, u x*correspondenceWeightedEllipticGenerator b (bakryEmeryGibbsWeight W) θ x
          ∂correspondenceBrascampLiebMeasure W) = 0 := by
      intro θ hθ hc
      let f : CorrespondenceBrascampLiebCompactTest E := ⟨θ, hθ, hc⟩
      have hI : inner ℝ u (correspondenceBrascampLiebCoreL2 W b hW f) =
          ∫ x, u x*bakryEmeryGibbsGenerator W b θ x
          ∂correspondenceBrascampLiebMeasure W := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [correspondenceBrascampLieb_core_ae W b hW f] with x hx
        rw [hx]
        simp [f, mul_comm]
      rw [correspondenceBrascampLieb_weighted_generator_eq W θ b (hW.of_le (by norm_num)),← hI]
      rw [real_inner_comm]
      exact hu _ ⟨f, rfl⟩
    obtain ⟨c, hc⟩ := correspondenceWeightedElliptic_annihilator_constant b
      (bakryEmeryGibbsWeight W) (Real.contDiff_exp.comp (hW.of_le (show (1 : ℕ∞ω) ≤ 2 by
          norm_num)).neg)
      (fun _ => Real.exp_pos _) u (Lp.memLp u) hAnn
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    apply Lp.ext
    have hOne : correspondenceBrascampLiebOneL2 W =ᵐ[correspondenceBrascampLiebMeasure W]
        (fun _ => (1 : ℝ)) :=
      (memLp_const (μ := correspondenceBrascampLiebMeasure W) (p := 2) (1 : ℝ)).coeFn_toLp
    filter_upwards [hc, hOne, Lp.coeFn_smul c (correspondenceBrascampLiebOneL2 W)] with x hcx h1x
        hsx
    rw [hsx, hcx]
    simp only [Pi.smul_apply, h1x, smul_eq_mul, mul_one]
  · exact correspondenceBrascampLieb_constants_orthogonal W b hW

omit [CompleteSpace E] [DecidableEq ι] in
theorem correspondenceBrascampLieb_core_dense_centered
    (W : E → ℝ) (b : OrthonormalBasis ι ℝ E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)] :
    (correspondenceBrascampLiebCoreRange W b hW).topologicalClosure =
      (ℝ ∙ correspondenceBrascampLiebOneL2 W)ᗮ := by
  classical
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    correspondenceBrascampLieb_core_orthogonal_constants W b hW]

end
end GinibrePoincare

/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebWeakDirichlet.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakAdjoint
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceBrascampLiebCoreDual
/-!
# Correspondence Brascamp Lieb weak Dirichlet

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_weak_dirichlet`.
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

omit [CompleteSpace E] in
theorem correspondenceBrascampLieb_compact_memLp
    (W f : E → ℝ) (hW : Continuous W) (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp f 2 (correspondenceBrascampLiebMeasure W) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply correspondenceBrascampLieb_integrable_compact W _ hW (hf.norm.pow 2)
  apply hc.mono
  intro x hx hz
  apply hx
  simp [hz]

/-- Physical ordinary weighted H¹ input: Lebesgue distributional gradients,
with values and gradient coordinates in the genuine Gibbs L² space. -/
def CorrespondenceBrascampLiebHasWeakGradient (u : E → ℝ) (G : E → ι → ℝ) (b : ι → E) : Prop :=
  ∀ i, CorrespondenceBrascampLiebHasWeakDerivative u (fun x => G x i) (b i)

omit [CompleteSpace E] [DecidableEq ι] in
theorem correspondenceBrascampLieb_weak_dirichlet
    (W u f : E → ℝ) (G : E → ι → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : ∀ i, CorrespondenceBrascampLiebLocallyL2 (fun x => G x i))
    (hw : CorrespondenceBrascampLiebHasWeakGradient u G b)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∫ x, u x*bakryEmeryGibbsGenerator W b f x ∂correspondenceBrascampLiebMeasure W) =
      -(∫ x, G x ⬝ᵥ correspondenceBrascampLiebGradient f b x
        ∂correspondenceBrascampLiebMeasure W) := by
  classical
  let μ := correspondenceBrascampLiebMeasure W
  let D := fun i => bakryEmeryGibbsDirectional f (b i)
  let L := fun i x => bakryEmeryGibbsDirectional (D i) (b i) x-
    bakryEmeryGibbsDirectional W (b i) x*D i x
  have hD (i : ι) : ContDiff ℝ 2 (D i) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf (b i)
  have hcD (i : ι) : HasCompactSupport (D i) := hc.fderiv_apply ℝ (b i)
  have hL (i : ι) : Continuous (L i) :=
    (correspondenceBrascampLieb_direction_contDiff (m := 1) (hD i) (b i)).continuous.sub
      ((correspondenceBrascampLieb_direction_contDiff (m := 1) hW (b i)).continuous.mul (hD
          i).continuous)
  have hcL (i : ι) : HasCompactSupport (L i) :=
    ((hcD i).fderiv_apply ℝ (b i)).sub (hcD i).mul_left
  have hiL (i : ι) : Integrable (fun x => u x*L i x) μ :=
    hu.integrable_mul (correspondenceBrascampLieb_compact_memLp W (L i) hW.continuous (hL i) (hcL
        i))
  have hiG (i : ι) : Integrable (fun x => G x i*D i x) μ := by
    apply (correspondenceWeightedElliptic_integrable_density (bakryEmeryGibbsWeight W) _
      (Real.continuous_exp.comp hW.continuous.neg) (fun _ => Real.exp_pos _)).mpr
    have hi := (correspondenceBrascampLieb_localL2_locallyIntegrable _ (hG
        i)).integrable_smul_right_of_hasCompactSupport
        ((Real.continuous_exp.comp hW.continuous.neg).mul (hD i).continuous)
        (hcD i).mul_left
    simpa only [smul_eq_mul, Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc,
      bakryEmeryGibbsWeight, Function.comp_apply, Pi.neg_apply] using hi
  have he (i : ι) : (∫ x, u x*L i x ∂μ) = -(∫ x, G x i*D i x ∂μ) := by
    have ha := correspondenceBrascampLieb_weak_weighted_adjoint W u (fun x => G x i) (b i)
      (hW.of_le (by norm_num)) hu (hG i) (hw i) (D i) ((hD i).of_le (by norm_num)) (hcD i)
    have heq : (fun x => u x*(bakryEmeryGibbsDirectional W (b i) x*D i x-
        bakryEmeryGibbsDirectional (D i) (b i) x)) = -(fun x => u x*L i x) := by
      funext x
      simp only [Pi.neg_apply, L]
      ring
    rw [heq] at ha
    change (∫ x, G x i*D i x ∂μ) = ∫ x, -(u x*L i x) ∂μ at ha
    rw [integral_neg] at ha
    linarith
  have hl : (∫ x, u x*bakryEmeryGibbsGenerator W b f x ∂μ) =
      ∑ i, ∫ x, u x*L i x ∂μ := by
    unfold bakryEmeryGibbsGenerator
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => hiL i)
  have hr : (∫ x, G x ⬝ᵥ correspondenceBrascampLiebGradient f b x ∂μ) =
      ∑ i, ∫ x, G x i*D i x ∂μ := by
    unfold dotProduct correspondenceBrascampLiebGradient
    exact integral_finsetSum _ (fun i _ => hiG i)
  rw [hl, hr]
  simp_rw [he]
  exact Finset.sum_neg_distrib _

end
end GinibrePoincare

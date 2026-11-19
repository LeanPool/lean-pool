/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreLinearStatisticDifferential.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreC1WeakPoincare
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Ginibre linear statistic differential

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `ginibreLinearStatistic_gradient_bound`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- The linear statistic `∑ i, g (z i)` of a configuration. -/
def ginibreLinearStatistic (n : ℕ) (g : ℂ → ℂ) (z : Configuration n) : ℂ := ∑ i, g (z i)

/-- Exact planar Euclidean gradient norm of a real linear functional. -/
theorem complexRealDual_norm_sq (L : ℂ →L[ℝ] ℝ) :
    ‖L‖^2=(L 1)^2+(L Complex.I)^2 := by
  simpa only [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    using Complex.orthonormalBasisOneI.norm_dual L

theorem ginibreLinearStatistic_contDiff {n : ℕ} (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (ginibreLinearStatistic n g) := by
  apply ContDiff.sum
  intro i hi
  exact hg.comp (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff

theorem ginibreLinearStatistic_fderiv_direction {n : ℕ} (g : ℂ → ℂ)
    (hg : ContDiff ℝ 1 g) (z : Configuration n) (j : Fin n) (a : ℂ) :
    fderiv ℝ (ginibreLinearStatistic n g) z (coordinateDirection j a)=fderiv ℝ g (z j) a := by
  have hgd := hg.differentiable (by norm_num)
  have hG : fderiv ℝ (ginibreLinearStatistic n g) z=
      ∑ i : Fin n, (fderiv ℝ g (z i)).comp (ContinuousLinearMap.proj i) := by
    have he : ginibreLinearStatistic n g=∑ i : Fin n, g ∘ (ContinuousLinearMap.proj i :
        Configuration n →L[ℝ] ℂ) := by
      funext z
      simp [ginibreLinearStatistic, Finset.sum_apply]
    rw [he, fderiv_sum (fun i hi => (hgd (z i)).comp z (ContinuousLinearMap.proj i : Configuration n
        →L[ℝ] ℂ).differentiableAt)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [fderiv_comp z (hgd (z i)) (ContinuousLinearMap.proj i : Configuration n →L[ℝ]
        ℂ).differentiableAt, ContinuousLinearMap.fderiv]
    rfl
  rw [hG, sum_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, coordinateDirection]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

/-- Exact chain rule in each particle's two real directions. -/
theorem ginibreLinearStatistic_chain_direction {n : ℕ} (g : ℂ → ℂ)
    (hg : ContDiff ℝ 1 g) (F : ℂ → ℝ) (hF : ContDiff ℝ 1 F)
    (z : Configuration n) (j : Fin n) (a : ℂ) :
    fderiv ℝ (fun z => F (ginibreLinearStatistic n g z)) z (coordinateDirection j a)=
      fderiv ℝ F (ginibreLinearStatistic n g z) (fderiv ℝ g (z j) a) := by
  change fderiv ℝ (F ∘ ginibreLinearStatistic n g) z (coordinateDirection j a)=_
  rw [fderiv_comp z ((hF.differentiable (by norm_num)) _)
    (((ginibreLinearStatistic_contDiff g hg).differentiable (by norm_num)) z),
    ContinuousLinearMap.comp_apply, ginibreLinearStatistic_fderiv_direction g hg]

/-- The genuine pointwise gradient bound, with the sharp factor n. -/
theorem ginibreLinearStatistic_gradient_bound {n : ℕ} (g : ℂ → ℂ)
    (hg : ContDiff ℝ 1 g) (K : ℝ≥0) (hLip : LipschitzWith K g)
    (F : ℂ → ℝ) (hF : ContDiff ℝ 1 F) (z : Configuration n) :
    realGradientNormSq (fun z => F (ginibreLinearStatistic n g z)) z ≤
      (n : ℝ)*(K : ℝ)^2*‖fderiv ℝ F (ginibreLinearStatistic n g z)‖^2 := by
  unfold realGradientNormSq
  have hpair (j : Fin n) :
      (fderiv ℝ (fun z => F (ginibreLinearStatistic n g z)) z (realCoordinateDirection j))^2+
      (fderiv ℝ (fun z => F (ginibreLinearStatistic n g z)) z (imaginaryCoordinateDirection j))^2 ≤
        (K : ℝ)^2*‖fderiv ℝ F (ginibreLinearStatistic n g z)‖^2 := by
    let L := (fderiv ℝ F (ginibreLinearStatistic n g z)).comp (fderiv ℝ g (z j))
    have hb : ‖L‖≤‖fderiv ℝ F (ginibreLinearStatistic n g z)‖*(K : ℝ) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _))
    rw [show realCoordinateDirection j=coordinateDirection j 1 from rfl,
      show imaginaryCoordinateDirection j=coordinateDirection j Complex.I from rfl,
      ginibreLinearStatistic_chain_direction g hg F hF,
      ginibreLinearStatistic_chain_direction g hg F hF]
    change (L 1)^2+(L Complex.I)^2≤_
    rw [← complexRealDual_norm_sq]
    nlinarith [norm_nonneg L, norm_nonneg (fderiv ℝ F (ginibreLinearStatistic n g z)), K.coe_nonneg]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j hj => hpair j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using
      hh

end
end GinibrePoincare

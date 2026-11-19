/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityLocalization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityProduct

/-! Multiplying the unknown by a genuine smooth compact cutoff preserves the
elliptic equation with explicit divergence data; the unknown is never differentiated. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E]

theorem ginibreLocalRegularity_localize_elliptic_equation
    {ι : Type*} [Fintype ι] (v : ι → E) (U : Set E)
    (u h : E → ℂ) (F : ι → E → ℂ)
    (hu : LocallyIntegrable u (volume : Measure E)) (hh : LocallyIntegrable h volume)
    (hF : ∀ i, LocallyIntegrable (F i) volume)
    (η : E → ℂ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (heq : ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, u x*ginibreLocalRegularityLaplacian v θ x) =
        (∫ x, h x*θ x)-∑ i, ∫ x, F i x*ginibreLocalRegularityDirectional (v i) θ x) :
    ∀ θ : E → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, (η x*u x)*ginibreLocalRegularityLaplacian v θ x) =
        (∫ x, (η x*h x-(∑ i, F i x*ginibreLocalRegularityDirectional (v i) η x)-
          u x*ginibreLocalRegularityLaplacian v η x)*θ x)-
        ∑ i, ∫ x, (η x*F i x+2*u x*ginibreLocalRegularityDirectional (v i) η x)*
          ginibreLocalRegularityDirectional (v i) θ x := by
  classical
  intro θ hθ hθc
  let A := fun x => u x*(η x*ginibreLocalRegularityLaplacian v θ x)
  let B := fun x => u x*(θ x*ginibreLocalRegularityLaplacian v η x)
  let C := fun i x => u x*(ginibreLocalRegularityDirectional (v i) η
      x*ginibreLocalRegularityDirectional (v i) θ x)
  let D := fun x => h x*(η x*θ x)
  let E' := fun i x => F i x*(η x*ginibreLocalRegularityDirectional (v i) θ x)
  let G := fun i x => F i x*(θ x*ginibreLocalRegularityDirectional (v i) η x)
  have htest (f : E → ℂ) (hf : LocallyIntegrable f volume) (q : E → ℂ)
      (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) : Integrable (fun x => f x*q x) volume := by
    simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport hq.continuous hqc
  have hDi (i) := ginibreLocalRegularityDirectional_smooth η hη (v i)
  have hDt (i) := ginibreLocalRegularityDirectional_smooth θ hθ (v i)
  have hLi := ginibreLocalRegularityLaplacian_smooth v η hη
  have hLt := ginibreLocalRegularityLaplacian_smooth v θ hθ
  have hA : Integrable A volume := htest u hu _ (hη.mul hLt) hηc.mul_right
  have hB : Integrable B volume := htest u hu _ (hθ.mul hLi) hθc.mul_right
  have hC (i) : Integrable (C i) volume := htest u hu _ ((hDi i).mul (hDt i))
    ((hηc.fderiv_apply ℝ (v i)).mul_right)
  have hD : Integrable D volume := htest h hh _ (hη.mul hθ) hηc.mul_right
  have hE (i) : Integrable (E' i) volume := htest (F i) (hF i) _ (hη.mul (hDt i)) hηc.mul_right
  have hG (i) : Integrable (G i) volume := htest (F i) (hF i) _ (hθ.mul (hDi i)) hθc.mul_right
  have hCS : Integrable (fun x => ∑ i, C i x) volume := integrable_finsetSum _ (fun i hi => hC i)
  have hES : Integrable (fun x => ∑ i, E' i x) volume := integrable_finsetSum _ (fun i hi => hE i)
  have hGS : Integrable (fun x => ∑ i, G i x) volume := integrable_finsetSum _ (fun i hi => hG i)
  have he := heq (η*θ) (hη.mul hθ) hηc.mul_right (tsupport_mul_subset_left.trans hηU)
  have hl : (∫ x, u x*ginibreLocalRegularityLaplacian v (η*θ) x) =
      (∫ x, A x)+(∫ x, B x)+2*(∑ i, ∫ x, C i x) := by
    calc
      _ = ∫ x, A x+B x+2*(∑ i, C i x) := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        dsimp only
        rw [ginibreLocalRegularityLaplacian_product v η θ hη hθ]
        dsimp only [A, B, C]
        rw [mul_add, mul_add]
        simp_rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        have he1 := integral_add (hA.add hB) (hCS.const_mul 2)
        have he2 := integral_add hA hB
        simp only [Pi.add_apply] at he1 he2
        rw [he1, he2, integral_const_mul, integral_finsetSum _ (fun i hi => hC i)]
  have hr (i) : (∫ x, F i x*ginibreLocalRegularityDirectional (v i) (η*θ) x) =
      (∫ x, E' i x)+(∫ x, G i x) := by
    calc
      _ = ∫ x, E' i x+G i x := by
        apply integral_congr_ae
        exact ae_of_all volume fun x => by
          dsimp only
          rw [ginibreLocalRegularityDirectional_product η θ hη hθ]
          dsimp only [E', G]
          ring
      _ = _ := integral_add (hE i) (hG i)
  rw [hl] at he
  simp_rw [hr, Finset.sum_add_distrib] at he
  have hd : (∫ x, h x*(η*θ) x)=∫ x, D x := rfl
  rw [hd] at he
  have hMain : (∫ x, (η x*u x)*ginibreLocalRegularityLaplacian v θ x)=∫ x, A x := by
    apply integral_congr_ae
    exact ae_of_all volume fun x => by dsimp [A]; ring
  have hH : (∫ x, (η x*h x-(∑ i, F i x*ginibreLocalRegularityDirectional (v i) η x)-
      u x*ginibreLocalRegularityLaplacian v η x)*θ x) =
      (∫ x, D x)-(∑ i, ∫ x, G i x)-(∫ x, B x) := by
    calc
      _ = ∫ x, D x-(∑ i, G i x)-B x := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        dsimp only
        dsimp only [D, G, B]
        rw [sub_mul, sub_mul, Finset.sum_mul]
        congr 1
        · congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro i hi
            ring
        · ring
      _ = _ := by
        have he1 := integral_sub (hD.sub hGS) hB
        have he2 := integral_sub hD hGS
        simp only [Pi.sub_apply] at he1 he2
        rw [he1, he2, integral_finsetSum _ (fun i hi => hG i)]
  have hV (i) : (∫ x, (η x*F i x+2*u x*ginibreLocalRegularityDirectional (v i) η x)*
      ginibreLocalRegularityDirectional (v i) θ x) = (∫ x, E' i x)+2*(∫ x, C i x) := by
    calc
      _ = ∫ x, E' i x+2*C i x := by
        apply integral_congr_ae
        exact ae_of_all volume fun x => by dsimp [E', C]; ring
      _ = _ := by rw [integral_add (hE i) ((hC i).const_mul 2), integral_const_mul]
  rw [hMain, hH]
  simp_rw [hV, Finset.sum_add_distrib,← Finset.mul_sum]
  linear_combination he

end
end GinibrePoincare

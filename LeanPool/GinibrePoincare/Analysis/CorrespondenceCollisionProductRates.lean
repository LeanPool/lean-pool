/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCollisionProductRates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCollisionProduct

/-!
# Correspondence collision product rates

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `correspondenceCollisionProduct_compact_rates`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

/-- The paper's finite product has the same fourth- and second-order compact
errors, with genuine value and ordinary-gradient integrals. -/
theorem correspondenceCollisionProduct_compact_rates {n : ℕ} (hn : 0 < n)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      (∫ z in K, |1-correspondenceCollisionProduct n ε z|^2 ∂ginibreMeasure n) ≤ C*ε^4 ∧
      (∫ z in K, ‖ginibreEuclideanGradient (correspondenceCollisionProduct n ε) z‖^2
        ∂ginibreMeasure n) ≤ C*ε^2 := by
  classical
  let := ginibreMeasure_isProbabilityMeasure hn
  choose C hC0 hC using fun p : VandermondePair n =>
    correspondenceCollisionCutoff_compact_rates hn p K hK
  let m : ℝ := Fintype.card (VandermondePair n)
  refine ⟨m * ∑ p, C p, mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun p hp => hC0 p)), ?_⟩
  intro ε hε
  have hc := correspondenceCollisionProduct_smooth n ε
  have hiv : IntegrableOn (fun z => |1-correspondenceCollisionProduct n ε z|^2)
      K (ginibreMeasure n) :=
    ((continuous_const.sub hc.continuous).abs.pow 2).continuousOn.integrableOn_compact hK
  have hig : IntegrableOn (fun z => ‖ginibreEuclideanGradient
      (correspondenceCollisionProduct n ε) z‖^2) K (ginibreMeasure n) :=
    ((continuous_ginibreEuclideanGradient _ hc).norm.pow 2).continuousOn.integrableOn_compact hK
  have hval (p : VandermondePair n) : IntegrableOn
      (fun z => |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2) K (ginibreMeasure n) :=
    ((continuous_const.sub (correspondenceCollisionCutoff_smooth _ _ _).continuous).abs.pow
        2).continuousOn.integrableOn_compact hK
  have hgrad (p : VandermondePair n) : IntegrableOn
      (fun z => ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2)
      K (ginibreMeasure n) :=
    ((continuous_ginibreEuclideanGradient _ (correspondenceCollisionCutoff_smooth _ _ _)).norm.pow
        2).continuousOn.integrableOn_compact hK
  have hvsum : IntegrableOn (fun z => m * ∑ p : VandermondePair n,
      |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2) K (ginibreMeasure n) :=
    (integrable_finsetSum _ (fun p hp => hval p)).const_mul m
  have hgsum : IntegrableOn (fun z => m * ∑ p : VandermondePair n,
      ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2)
      K (ginibreMeasure n) := (integrable_finsetSum _ (fun p hp => hgrad p)).const_mul m
  constructor
  · calc
      _ ≤ ∫ z in K, m * ∑ p : VandermondePair n,
          |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2 ∂ginibreMeasure n :=
        setIntegral_mono_on hiv hvsum hK.measurableSet
          (fun z hz => correspondenceCollisionProduct_value_bound n ε z)
      _ = m * ∑ p : VandermondePair n, ∫ z in K,
          |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2 ∂ginibreMeasure n := by
        rw [integral_const_mul, integral_finsetSum _ (fun p hp => hval p)]
      _ ≤ m * ∑ p : VandermondePair n, C p * ε^4 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p hp => (hC p ε hε).1)) (Nat.cast_nonneg
            _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  · calc
      _ ≤ ∫ z in K, m * ∑ p : VandermondePair n,
          ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2
          ∂ginibreMeasure n :=
        setIntegral_mono_on hig hgsum hK.measurableSet
          (fun z hz => correspondenceCollisionProduct_gradient_bound n ε z)
      _ = m * ∑ p : VandermondePair n, ∫ z in K,
          ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2
          ∂ginibreMeasure n := by
        rw [integral_const_mul, integral_finsetSum _ (fun p hp => hgrad p)]
      _ ≤ m * ∑ p : VandermondePair n, C p * ε^2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p hp => (hC p ε hε).2)) (Nat.cast_nonneg
            _)
      _ = _ := by rw [← Finset.sum_mul]; ring

end
end GinibrePoincare


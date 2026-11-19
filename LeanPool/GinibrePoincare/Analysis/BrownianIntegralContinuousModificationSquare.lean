/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianIntegralContinuousModificationSquare.lean.
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

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Brownian integral continuous modification square

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `realMartingale_finite_maximal_le`, `realMartingale_monotone_sampling`,
`realMartingale_memLp_two_of_le`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
variable {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]

/-- The actual square of any square-integrable real martingale is a submartingale. -/
theorem realMartingale_square_submartingale (P : Measure Ω)
    (ℱ : Filtration ι ‹MeasurableSpace Ω›) (M : ι → Ω → ℝ)
    (hM : Martingale M ℱ P) (hL2 : ∀ i, MemLp (M i) 2 P) :
    Submartingale (fun i ω => (M i ω)^2) ℱ P := by
  refine ⟨?_,?_, fun i => (hL2 i).integrable_sq⟩
  · intro i
    exact (show Continuous (fun r : ℝ => r^2) by fun_prop).comp_stronglyMeasurable (hM.1 i)
  · intro i j hij
    have hj := _root_.Integrable.norm_condExp_rpow_le
      (f := M j) (μ := P) (m := ℱ i) (p := 2) (by norm_num)
      (show Integrable (fun ω => ‖M j ω‖^(2 : ℝ)) P by
        simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using (hL2 j).integrable_sq)
    have he := hM.2 i j hij
    filter_upwards [hj, he] with ω hω he
    simpa [he, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hω

/-- Genuine finite-grid maximal second-moment estimate derived from conditional
Jensen and Doob's maximal inequality. -/
theorem realMartingale_finite_maximal_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P) (hL2 : ∀ i, MemLp (M i) 2 P)
    (ε : ℝ≥0) (n : ℕ) :
    (ε : ℝ≥0∞)^2 * P {ω | ∃ k ≤ n, (ε : ℝ) ≤ ‖M k ω‖} ≤
      ENNReal.ofReal (∫ ω, (M n ω)^2 ∂P) := by
  have hsq := realMartingale_square_submartingale P ℱ M hM hL2
  have hd := maximal_ineq hsq (fun i ω => sq_nonneg (M i ω)) (ε := ε^2) n
  have hsub : {ω | ∃ k ≤ n, (ε : ℝ) ≤ ‖M k ω‖} ⊆
      {ω | ((ε^2 : ℝ≥0) : ℝ) ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
        (fun k => (M k ω)^2)} := by
    intro ω hω
    obtain ⟨k, hkn, hk⟩ := hω
    change ((ε^2 : ℝ≥0) : ℝ) ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
      (fun k => (M k ω)^2)
    apply (Finset.le_sup'_iff Finset.nonempty_range_add_one).mpr
    refine ⟨k, Finset.mem_range.mpr (by omega),?_⟩
    have hsq' := sq_le_sq₀ ε.coe_nonneg (norm_nonneg (M k ω))
    have hh : (ε : ℝ)^2 ≤ ‖M k ω‖^2 := hsq'.mpr hk
    simpa [Real.norm_eq_abs, sq_abs] using hh
  calc
    _ ≤ ((ε^2 : ℝ≥0) : ℝ≥0∞) * P {ω | ((ε^2 : ℝ≥0) : ℝ) ≤
        (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => (M k ω)^2)} := by
      simp only [ENNReal.coe_pow]
      gcongr
    _ ≤ _ := hd
    _ ≤ _ := ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hL2 n).integrable_sq
      (ae_of_all _ (fun ω => sq_nonneg (M n ω))))

/-- The genuine finite-grid maximal probability bound in the usual quotient form. -/
theorem realMartingale_finite_maximal_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P) (hL2 : ∀ i, MemLp (M i) 2 P)
    (ε : ℝ≥0) (hε : 0 < ε) (n : ℕ) :
    P {ω | ∃ k ≤ n, (ε : ℝ) ≤ ‖M k ω‖} ≤
      ENNReal.ofReal (∫ ω, (M n ω)^2 ∂P)/(ε : ℝ≥0∞)^2 := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero 2 (by exact_mod_cast hε.ne')))
    (Or.inl (ENNReal.pow_ne_top (by simp)))).mpr
  simpa only [mul_comm] using realMartingale_finite_maximal_mul_le P ℱ M hM hL2 ε n

/-- Actual monotone sampling preserves a genuine martingale and its filtration. -/
def sampledMartingaleFiltration {J : Type*} [Preorder J]
    (ℱ : Filtration ι ‹MeasurableSpace Ω›) (τ : J → ι) (hτ : Monotone τ) :
    Filtration J ‹MeasurableSpace Ω› := ⟨fun i => ℱ (τ i), ℱ.mono'.comp hτ, fun i => ℱ.le (τ i)⟩

theorem realMartingale_monotone_sampling {J : Type*} [Preorder J]
    (P : Measure Ω) (ℱ : Filtration ι ‹MeasurableSpace Ω›) (M : ι → Ω → ℝ)
    (hM : Martingale M ℱ P) (τ : J → ι) (hτ : Monotone τ) :
    Martingale (fun i => M (τ i)) (sampledMartingaleFiltration ℱ τ hτ) P :=
  ⟨fun i => hM.1 (τ i), fun _i _j hij => hM.2 _ _ (hτ hij)⟩

/-- The genuine terminal L² hypothesis supplies every earlier L² marginal. -/
theorem realMartingale_memLp_two_of_le (P : Measure Ω)
    (ℱ : Filtration ι ‹MeasurableSpace Ω›) (M : ι → Ω → ℝ)
    (hM : Martingale M ℱ P) (T t : ι) (ht : t ≤ T) (hT : MemLp (M T) 2 P) :
    MemLp (M t) 2 P := by
  have hc : MemLp (P[M T | ℱ t]) 2 P := hT.condExp (by norm_num)
  exact (memLp_congr_ae (hM.2 t T ht)).mp hc

end
end GinibrePoincare

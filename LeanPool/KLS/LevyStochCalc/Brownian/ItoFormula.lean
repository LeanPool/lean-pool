/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use
-- `continuous_abs.measurable.comp` for the no longer reachable `Measurable.abs`.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFormulaGrid
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoRiemannIntegrand
public import LeanPool.KLS.LevyStochCalc.Brownian.TaylorTwo

/-!
# Grid Riemann sums of the Itô integral

The weighted sum of the Itô integral's increments across a uniform grid is itself an Itô
integral — that of the grid's step weight against the integrand — and replacing the step weight
by a general one costs the `L²` distance between them times the bound on the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae` — the grid-weighted sum of increments as
  an Itô integral.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sum_unifGrid_sub_le` — that sum is `L²`-close to the
  Itô integral of the weight, with the weight's modulus of continuity as the rate.
* `LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le` — the second-order Taylor
  remainder along a uniform grid is `O(m^{-1/2})` in `L¹`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section GridSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in
/-- **The grid-weighted sum of the Itô integral's increments is an Itô integral.** For
coefficients `ξ i` measurable at the left endpoint of cell `i` of the uniform grid,

  `∑ᵢ ξᵢ · (M_{tᵢ₊₁} − M_{tᵢ}) = ∫_0^T G_m(s)·H_s dW_s`

almost surely, where `G_m` is the step process with value `ξ i` on `(tᵢ, tᵢ₊₁]`. -/
theorem sum_unifGrid_mul_sub_ae {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    (fun ω => ∑ i : Fin m, ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
          (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
        (fun T' hT' =>
          (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).lintegral_eval_mul_sq_lt_top
            hq T' hT') T := by
  have hlast : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition
      (Fin.last (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).N) ≤ T :=
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition_le_T
  exact sum_xi_mul_stochasticIntegral_sub_ae W ℱ hℱ
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas)
    (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) H hm hp hq _ _ _ hT hlast

include hℱ in
/-- **The martingale Riemann sum is `L²`-close to the Itô integral of the weight.** If the cell
coefficients are a weight `g` frozen at the grid's left endpoints and `g` varies by at most `ε`
over the mesh, then

  `‖∑ᵢ g(tᵢ)·ΔMᵢ − ∫_0^T g_s H_s dW_s‖_{L²}² ≤ C²·ε²·T`. -/
theorem lintegral_sq_sum_unifGrid_sub_le
    (g : Ω → ℝ → ℝ)
    (hmg : Measurable (Function.uncurry fun ω s => g ω s * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g ω s * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i))
    (hξg : ∀ (i : Fin m) (ω : Ω), ξ i ω = g ω (unifGrid T m (i : ℕ)))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hmod : ∀ ω : Ω, ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
      |x - y| ≤ T / (m : ℝ) → |g ω x - g ω y| ≤ ε) :
    ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => g ω s * H ω s) hmg hpg hqg T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (ε ^ 2 * T) := by
  have hstep := sum_unifGrid_mul_sub_ae W ℱ hℱ H hm hp hq hT hm0 ξ hbdd hmeas hadapt
  have hcongr : ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => g ω s * H ω s) hmg hpg hqg T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
            (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
          (fun T' hT' =>
            (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).lintegral_eval_mul_sq_lt_top
              hq T' hT') T ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => g ω s * H ω s) hmg hpg hqg T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with ω hω
    rw [hω]
  rw [hcongr]
  refine le_trans (lintegral_sq_stochasticIntegral_mul_sub_le W ℱ hℱ H
    (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω) g _ _ _
    hmg hpg hqg hC0 hCH hT) ?_
  refine mul_le_mul_right ?_ _
  refine lintegral_sq_sub_le_of_bound
    (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω) g hε0 ?_
  intro ω s hs
  exact abs_ofUnifGrid_eval_sub_le hT hm0 ξ hbdd hmeas g hξg hmod ω hs

end GridSum

section TaylorRemainder

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- **The second-order Taylor remainder of an Itô process along a uniform grid is `O(m^{-1/2})`
in `L¹`.** -/
theorem integral_abs_taylorRemainder_le
    {X₀ : Ω → ℝ} (hX₀ : Measurable X₀) (bdrift : Ω → ℝ → ℝ)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => taylorRemainder f f' f''
        (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainder f f' f''
          (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ K * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
          + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
            * (T * Real.sqrt (T / (m : ℝ))))) := by
  have hX : ∀ i : ℕ, Measurable (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i)) :=
    fun i => measurable_itoProcess W ℱ hℱ H hm hp hq hX₀ hbm _
  have hfd : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hf'd : Differentiable ℝ f' := fun x => (hf' x).differentiableAt
  have hfc : Continuous f := hfd.continuous
  have hf'c : Continuous f' := hf'd.continuous
  have hf''c : Continuous f'' := by
    have hlip : LipschitzWith (Real.toNNReal K) f'' := by
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0]
      exact hf'' u v
    exact hlip.continuous
  -- the remainder is measurable
  have hR : Measurable fun ω => taylorRemainder f f' f''
      (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m := by
    unfold taylorRemainder
    refine ((hfc.measurable.comp (hX m)).sub (hfc.measurable.comp (hX 0))).sub
      ((Finset.measurable_sum _ fun i _ => (hf'c.measurable.comp (hX i)).mul
          ((hX (i + 1)).sub (hX i))).add
        (Finset.measurable_sum _ fun i _ =>
          ((hf''c.measurable.comp (hX i)).mul (((hX (i + 1)).sub (hX i)).pow_const 2)).div_const 2))
  -- the pathwise Taylor bound
  have hptw : ∀ ω : Ω, |taylorRemainder f f' f''
      (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m|
      ≤ K * ∑ i ∈ Finset.range m,
        |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m (i + 1)) ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω| ^ 3 :=
    fun ω => abs_taylorRemainder_le hK0 hf hf' hf'' _ m
  -- the increment splits into drift and martingale parts
  have hsplit : ∀ (i : ℕ) (ω : Ω),
      itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m (i + 1)) ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω
        = (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω) := fun i ω =>
    itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB (unifGrid_nonneg hT.le m i)
      (unifGrid_lt_succ hT hm0 i).le ω
  have hterm : ∀ i ∈ Finset.range m, MeasureTheory.Integrable (fun ω : Ω =>
      |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m (i + 1)) ω
        - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω| ^ 3) P := by
    intro i _
    simp_rw [hsplit i]
    exact integrable_abs_itoIncrement_pow_three W ℱ hℱ H hm hp hq hC0 hCH bdrift hbm hB0 hB
      (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
  have hsumint : MeasureTheory.Integrable (fun ω : Ω => K * ∑ i ∈ Finset.range m,
      |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m (i + 1)) ω
        - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ hterm).const_mul K
  have hRint : MeasureTheory.Integrable (fun ω : Ω => |taylorRemainder f f' f''
      (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m|) P := by
    refine hsumint.mono (continuous_abs.measurable.comp hR).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hptw ω).trans (le_abs_self _)
  have hRint0 : MeasureTheory.Integrable (fun ω : Ω => taylorRemainder f f' f''
      (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m) P := by
    refine hsumint.mono hR.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hptw ω).trans (le_abs_self _)
  refine ⟨hRint0, ?_⟩
  calc ∫ ω, |taylorRemainder f f' f''
        (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m| ∂P
      ≤ ∫ ω, K * ∑ i ∈ Finset.range m,
          |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m (i + 1)) ω
            - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω| ^ 3 ∂P :=
        MeasureTheory.integral_mono hRint hsumint hptw
    _ = K * ∑ i ∈ Finset.range m, ∫ ω,
          |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m (i + 1)) ω
            - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω| ^ 3 ∂P := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ hterm]
    _ ≤ K * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        simp_rw [hsplit]
        exact sum_integral_abs_itoIncrement_pow_three_le W ℱ hℱ H hm hp hq hC0 hCH bdrift hbm
          hB0 hB hT hm0

end TaylorRemainder

end LevyStochCalc.Brownian.Ito

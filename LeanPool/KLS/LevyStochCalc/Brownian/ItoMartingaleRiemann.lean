/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoProcessWindow
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoGridPartition
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFormula

/-!
# The martingale Riemann sum of the Itô formula

Freezing a Lipschitz function of a continuous Itô process at the left endpoints of a uniform
grid and pairing it with the Itô integral's increments gives a Riemann sum for
`∫_0^T φ(X_s)·H_s dW_s`, with an `L²` error of order `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top` — a bounded weight preserves the
  `L²` bound on an integrand.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_frozen_sub_le` — the `L²` distance
  between the frozen step weight and the weight itself.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le` — the `L²`
  error of the martingale Riemann sum.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The square of a real number's extended norm is the extended value of its square. -/
theorem sq_enn_nnnorm_eq_ofReal_sq (x : ℝ) :
    ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
    rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
    exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
  rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]

section Weight

variable {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}

omit [IsProbabilityMeasure P] in
/-- Multiplying an `L²` integrand by a bounded weight keeps it `L²`. -/
theorem lintegral_sq_bounded_mul_lt_top
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {g : Ω → ℝ → ℝ} {Kg : ℝ} (hKg0 : 0 ≤ Kg) (hKg : ∀ ω s, |g ω s| ≤ Kg) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  have hgle : ∀ (ω : Ω) (s : ℝ), (‖g ω s‖₊ : ℝ≥0∞) ≤ (Real.toNNReal Kg : ℝ≥0∞) := by
    intro ω s
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal Kg hKg0, coe_nnNorm, Real.norm_eq_abs]
    exact hKg ω s
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ (Real.toNNReal Kg : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    rw [nnNorm_mul, ENNReal.coe_mul, mul_pow]
    gcongr
    exact ENNReal.coe_le_coe.mp (hgle ω s)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (Real.toNNReal Kg : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = (Real.toNNReal Kg : ℝ≥0∞) ^ 2
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        have hne : ((Real.toNNReal Kg : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
        rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
        exact lintegral_congr fun ω =>
          MeasureTheory.lintegral_const_mul' _ _ hne
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (hq T hT)

end Weight

section Frozen

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in
/-- **The frozen step weight is `L²`-close to the weight itself.** For a Lipschitz `φ`, the
step process taking the value `φ(X_{tᵢ})` on cell `i` differs from `φ(X_s)` by
`L²·T·(2B²(T/m)² + 2C²(T/m))` in `L²(P ⊗ ds)`. -/
theorem IsItoVersion.lintegral_sq_frozen_sub_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hξ : ∀ (i : Fin m) (ω : Ω), ξ i ω = φ (X (unifGrid T m (i : ℕ)) ω)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * (C ^ 2 * (T / (m : ℝ))))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  have hsub : Measurable (Function.uncurry fun ω s =>
      (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω - φ (X s ω)) :=
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval.sub
      (h.measurable_uncurry_comp hφc.measurable)
  have hjoint : Measurable (Function.uncurry fun ω s =>
      (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
        - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2) :=
    (hsub.nnNorm.coe_nnreal_ennreal).pow_const 2
  have hmeasCell : ∀ i : ℕ, Measurable fun ω : Ω =>
      ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume := fun i =>
    hjoint.lintegral_prod_right'
  -- decompose the time integral over the grid cells
  rw [lintegral_congr fun ω => lintegral_Icc_eq_sum_unifGrid hT hm0
    (fun s => (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
      - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2)]
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeasCell i]
  -- on each cell the step process is frozen at the left endpoint
  have hcell : ∀ i ∈ Finset.range m,
      ∫⁻ ω, ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
          (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
            - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal ((T / (m : ℝ)) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * (C ^ 2 * (T / (m : ℝ))))) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hfrozen : ∀ (ω : Ω), ∀ s ∈ Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (L ^ 2)
          * ENNReal.ofReal ((X s ω - X (unifGrid T m i) ω) ^ 2) := by
      intro ω s hs
      have heval : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          = φ (X (unifGrid T m i) ω) := by
        have := SimplePredictable.ofUnifGrid_eval hT hm0 ξ hbdd hmeas ⟨i, him⟩ ⟨hs.1, hs.2⟩ ω
        rw [this, hξ ⟨i, him⟩ ω]
      rw [heval, sq_enn_nnnorm_eq_ofReal_sq, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hlip := hφlip (X (unifGrid T m i) ω) (X s ω)
      have habs : |X (unifGrid T m i) ω - X s ω| = |X s ω - X (unifGrid T m i) ω| :=
        abs_sub_comm _ _
      rw [habs] at hlip
      calc (φ (X (unifGrid T m i) ω) - φ (X s ω)) ^ 2
          = |φ (X (unifGrid T m i) ω) - φ (X s ω)| ^ 2 := (sq_abs _).symm
        _ ≤ (L * |X s ω - X (unifGrid T m i) ω|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hlip 2
        _ = L ^ 2 * (X s ω - X (unifGrid T m i) ω) ^ 2 := by
            rw [mul_pow, sq_abs]
    calc ∫⁻ ω, ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
          (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
            - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
            ENNReal.ofReal (L ^ 2)
              * ENNReal.ofReal ((X s ω - X (unifGrid T m i) ω) ^ 2) ∂volume ∂P :=
          lintegral_mono fun ω =>
            MeasureTheory.setLIntegral_mono' measurableSet_Ioc (hfrozen ω)
      _ = ENNReal.ofReal (L ^ 2) * ∫⁻ ω,
            ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              ENNReal.ofReal ((X s ω - X (unifGrid T m i) ω) ^ 2) ∂volume ∂P := by
          have hne : ENNReal.ofReal (L ^ 2) ≠ ⊤ := by simp
          rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
          exact lintegral_congr fun ω => MeasureTheory.lintegral_const_mul' _ _ hne
      _ ≤ ENNReal.ofReal (L ^ 2)
            * ENNReal.ofReal ((T / (m : ℝ)) * (2 * (B * (T / (m : ℝ))) ^ 2
              + 2 * (C ^ 2 * (T / (m : ℝ))))) := by
          gcongr
          have := h.lintegral_window_sq_sub_le hC0 hCH hbm hB0 hB
            (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i).le
          rwa [unifGrid_succ_sub hm0 i] at this
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, mul_comm ((m : ℝ≥0∞))]
  rw [mul_assoc]
  gcongr _ * ?_
  have hWnn : (0 : ℝ) ≤ 2 * (B * (T / (m : ℝ))) ^ 2 + 2 * (C ^ 2 * (T / (m : ℝ))) := by
    positivity
  rw [show ((m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ)) from (ENNReal.ofReal_natCast m).symm,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  field_simp

include hC0 hCH in
/-- **The martingale Riemann sum converges in `L²` at rate `√(T/m)`.** Freezing a bounded
Lipschitz `φ(X)` at the grid's left endpoints and pairing it with the Itô integral's increments
approximates `∫_0^T φ(X_s) H_s dW_s` with squared `L²` error
`C²·L²·T·(2B²(T/m)² + 2C²(T/m))`. -/
theorem IsItoVersion.lintegral_sq_martingaleRiemann_sub_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => φ (X s ω) * H ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * (C ^ 2 * (T / (m : ℝ)))))) := by
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  set ξ : Fin m → Ω → ℝ := fun i ω => φ (X (unifGrid T m (i : ℕ)) ω) with hξdef
  have hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M := fun i => ⟨Kφ, fun ω => hφbd _⟩
  have hmeas : ∀ i : Fin m, Measurable (ξ i) := fun i =>
    hφc.measurable.comp (h.measurable (unifGrid T m (i : ℕ)))
  have hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (unifGrid T m (i : ℕ)))
  have hstep := sum_unifGrid_mul_sub_ae W ℱ hℱ H hm hp hq hT hm0 ξ hbdd hmeas hadapt
  have hcongr : ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => φ (X s ω) * H ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
            (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
          (fun T' hT' =>
            (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).lintegral_eval_mul_sq_lt_top
              hq T' hT') T ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => φ (X s ω) * H ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with ω hω
    rw [hω]
  rw [hcongr]
  refine le_trans (lintegral_sq_stochasticIntegral_mul_sub_le W ℱ hℱ H
    (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω)
    (fun ω s => φ (X s ω)) _ _ _ hmg hpg hqg hC0 hCH hT) ?_
  gcongr _ * ?_
  exact h.lintegral_sq_frozen_sub_le hC0 hCH hbm hB0 hB hL0 hφlip hT hm0 ξ hbdd hmeas
    fun i ω => rfl

end Frozen

end LevyStochCalc.Brownian.Ito

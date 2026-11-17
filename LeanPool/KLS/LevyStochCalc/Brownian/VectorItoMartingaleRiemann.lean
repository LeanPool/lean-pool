/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoProcessWindow
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoMartingaleRiemann

/-!
# The martingale Riemann sum along a vector Itô process

Freezing a Lipschitz function of a continuous vector Itô process at the left endpoints of a
uniform grid and pairing it with the increments of an Itô integral against one Brownian
coordinate gives a Riemann sum for `∫_0^T φ(X_s)·G_s dWᵏ_s`, with an `L²` error of order
`√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_frozen_sub_le` — the `L²` distance
  between the frozen step weight and the weight itself.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le` — the
  `L²` error of the martingale Riemann sum.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorFrozen

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in
/-- **The frozen step weight is `L²`-close to the weight itself.** For an `L`-Lipschitz `φ` on the
state space, the step process taking the value `φ(X_{tᵢ})` on cell `i` differs from `φ(X_s)` by
`L²·T·n(2B²(T/m)² + 2d²C²(T/m))` in `L²(P ⊗ ds)`. -/
theorem IsVectorItoVersion.lintegral_sq_frozen_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hξ : ∀ (i : Fin m) (ω : Ω), ξ i ω = φ (X (unifGrid T m (i : ℕ)) ω)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  have hsub : Measurable (Function.uncurry fun ω s =>
      (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω - φ (X s ω)) :=
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval.sub
      (h.measurable_uncurry_comp hφc.measurable)
  have hjoint : Measurable (Function.uncurry fun ω s =>
      (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
        - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2) :=
    (hsub.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hmeasCell : ∀ i : ℕ, Measurable fun ω : Ω =>
      ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume := fun i =>
    hjoint.lintegral_prod_right'
  rw [lintegral_congr fun ω => lintegral_Icc_eq_sum_unifGrid hT hm0
    (fun s => (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
      - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2)]
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeasCell i]
  have hcell : ∀ i ∈ Finset.range m,
      ∫⁻ ω, ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
          (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
            - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hfrozen : ∀ (ω : Ω), ∀ s ∈ Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (L ^ 2)
          * ENNReal.ofReal (‖X s ω - X (unifGrid T m i) ω‖ ^ 2) := by
      intro ω s hs
      have heval : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          = φ (X (unifGrid T m i) ω) := by
        have := SimplePredictable.ofUnifGrid_eval hT hm0 ξ hbdd hmeas ⟨i, him⟩ ⟨hs.1, hs.2⟩ ω
        rw [this, hξ ⟨i, him⟩ ω]
      rw [heval, sq_enn_nnnorm_eq_ofReal_sq, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hlip := hφlip (X (unifGrid T m i) ω) (X s ω)
      have hnrm : ‖X (unifGrid T m i) ω - X s ω‖ = ‖X s ω - X (unifGrid T m i) ω‖ :=
        norm_sub_rev _ _
      rw [hnrm] at hlip
      calc (φ (X (unifGrid T m i) ω) - φ (X s ω)) ^ 2
          = |φ (X (unifGrid T m i) ω) - φ (X s ω)| ^ 2 := (sq_abs _).symm
        _ ≤ (L * ‖X s ω - X (unifGrid T m i) ω‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hlip 2
        _ = L ^ 2 * ‖X s ω - X (unifGrid T m i) ω‖ ^ 2 := by rw [mul_pow]
    calc ∫⁻ ω, ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
          (‖(SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
            - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
            ENNReal.ofReal (L ^ 2)
              * ENNReal.ofReal (‖X s ω - X (unifGrid T m i) ω‖ ^ 2) ∂volume ∂P :=
          lintegral_mono fun ω =>
            MeasureTheory.setLIntegral_mono' measurableSet_Ioc (hfrozen ω)
      _ = ENNReal.ofReal (L ^ 2) * ∫⁻ ω,
            ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              ENNReal.ofReal (‖X s ω - X (unifGrid T m i) ω‖ ^ 2) ∂volume ∂P := by
          have hne : ENNReal.ofReal (L ^ 2) ≠ ⊤ := by simp
          rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
          exact lintegral_congr fun ω => MeasureTheory.lintegral_const_mul' _ _ hne
      _ ≤ ENNReal.ofReal (L ^ 2)
            * ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
              + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))) := by
          gcongr
          have := h.lintegral_window_sq_norm_sub_le hC0 hCH hbm hB0 hB
            (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i).le
          rwa [unifGrid_succ_sub hm0 i] at this
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, mul_comm ((m : ℝ≥0∞))]
  rw [mul_assoc]
  gcongr _ * ?_
  have hWnn : (0 : ℝ) ≤ (n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
      + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))) := by positivity
  rw [show ((m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ)) from (ENNReal.ofReal_natCast m).symm,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  field_simp

include hC0 hCH in
/-- **The martingale Riemann sum converges in `L²` at rate `√(T/m)`.** Freezing a bounded
`L`-Lipschitz `φ(X)` at the grid's left endpoints and pairing it with the increments of
`∫ G dWᵏ` approximates `∫_0^T φ(X_s) G_s dWᵏ_s` with squared `L²` error
`C_G²·L²·T·n(2B²(T/m)² + 2d²C²(T/m))`. -/
theorem IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    (k : Fin d) {G : Ω → ℝ → ℝ} (hGm : Measurable (Function.uncurry G))
    (hGp : Probability.ProgressivelyMeasurable ℱ G)
    (hGs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {CG : ℝ} (hCG0 : 0 ≤ CG) (hCG : ∀ ω s, |G ω s| ≤ CG)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * G ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * G ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (CG ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  set ξ : Fin m → Ω → ℝ := fun i ω => φ (X (unifGrid T m (i : ℕ)) ω) with hξdef
  have hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M := fun i => ⟨Kφ, fun ω => hφbd _⟩
  have hmeas : ∀ i : Fin m, Measurable (ξ i) := fun i =>
    hφc.measurable.comp (h.measurable (unifGrid T m (i : ℕ)))
  have hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (unifGrid T m (i : ℕ)))
  have hstep := sum_unifGrid_mul_sub_ae (W.W k) ℱ (hcoord k) G hGm hGp hGs hT hm0 ξ hbdd hmeas
    hadapt
  have hcongr : ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
          * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * G ω s)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hGm)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
            (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hGp)
          (fun T' hT' =>
            (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).lintegral_eval_mul_sq_lt_top
              hGs T' hT') T ω
        - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with ω hω
    rw [hω]
  rw [hcongr]
  refine le_trans (lintegral_sq_stochasticIntegral_mul_sub_le (W.W k) ℱ (hcoord k) G
    (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω)
    (fun ω s => φ (X s ω)) _ _ _ hmg hpg hqg hCG0 hCG hT) ?_
  gcongr _ * ?_
  exact h.lintegral_sq_frozen_sub_le hC0 hCH hbm hB0 hB hL0 hφlip hT hm0 ξ hbdd hmeas
    fun i ω => rfl

end VectorFrozen

end LevyStochCalc.Brownian.Ito

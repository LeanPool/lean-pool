/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoQuadVarRiemann
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoMartingaleRiemann
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFormula

/-!
# Itô's formula for a scalar Itô process

For a continuous adapted version `X` of `X₀ + ∫ b ds + ∫ H dW` with bounded coefficients and
`f` twice differentiable with bounded derivatives and a Lipschitz second derivative,

  `f(X_T) − f(X_0) = ∫_0^T f'(X_s) b_s ds + ∫_0^T f'(X_s) H_s dW_s
      + ½ ∫_0^T f''(X_s) H_s² ds`

almost surely. The proof telescopes the second-order Taylor expansion over a uniform grid and
bounds the four resulting errors, all of which vanish as the mesh does.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoGridError` — the `L¹` error of the grid approximation, as a
  function of the mesh.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le` — that error bounds the
  `L¹` defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.itoFormula` — Itô's formula.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The mean value theorem in the form used here: a bound on the derivative is a Lipschitz
constant. -/
theorem abs_sub_le_of_hasDerivAt_bound {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    {K : ℝ} (hK : ∀ x, |g' x| ≤ K) (x y : ℝ) : |g x - g y| ≤ K * |x - y| := by
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (s := Set.univ) (C := K)
    (fun z _ => (hg z).hasDerivWithinAt)
    (fun z _ => by rw [Real.norm_eq_abs]; exact hK z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt

/-- From an `L²` bound in extended form, the first absolute moment is at most `√V`. -/
theorem integral_abs_le_sqrt_of_lintegral_sq_le {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.AEStronglyMeasurable g P) {V : ℝ} (hV0 : 0 ≤ V)
    (hle : ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal V) :
    MeasureTheory.Integrable g P ∧ ∫ ω, |g ω| ∂P ≤ Real.sqrt V := by
  have hmem : MeasureTheory.MemLp g 2 P :=
    memLp_two_of_lintegral_sq_lt_top hg (lt_of_le_of_lt hle (by simp))
  have hint : MeasureTheory.Integrable g P := hmem.integrable (by norm_num)
  have hsq : MeasureTheory.Integrable (fun ω => g ω ^ 2) P := by
    have hmul := hmem.integrable_mul hmem
    have hfun : (fun ω => g ω ^ 2) = g * g := by
      funext ω
      simp [pow_two]
    rw [hfun]
    exact hmul
  have hsqnn : ∀ ω : Ω, (0 : ℝ) ≤ g ω ^ 2 := fun ω => sq_nonneg _
  have hkey : ENNReal.ofReal (∫ ω, g ω ^ 2 ∂P) ≤ ENNReal.ofReal V := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsq
      (Filter.Eventually.of_forall hsqnn)]
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hle
    exact (sq_enn_nnnorm_eq_ofReal_sq (g ω)).symm
  refine ⟨hint, integral_abs_le_sqrt_of_integral_sq_le hint.abs hsq ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hV0).mp hkey

/-- The `L¹` error of the uniform-grid approximation in Itô's formula, as a function of the
mesh. -/
noncomputable def itoGridError (B C T K K₂ : ℝ) (x : ℝ) : ℝ :=
  K * (4 * (B ^ 3 * T * x ^ 2
      + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt x)))
    + K₂ * B * (T * (B * x + C * Real.sqrt x))
    + Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * (2 * (B * x) ^ 2 + 2 * (C ^ 2 * x)))))
    + 1 / 2 * (K₂ * (B ^ 2 * T * x)
        + 2 * K₂ * B * C * T * Real.sqrt x
        + Real.sqrt (K₂ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4) * (T * x))
        + K * C ^ 2 * (T * (B * x + C * Real.sqrt x)))

@[simp] theorem itoGridError_zero (B C T K K₂ : ℝ) : itoGridError B C T K K₂ 0 = 0 := by
  simp [itoGridError]

theorem continuous_itoGridError (B C T K K₂ : ℝ) :
    Continuous (itoGridError B C T K K₂) := by
  unfold itoGridError
  fun_prop

theorem tendsto_itoGridError (B C T K K₂ : ℝ) :
    Filter.Tendsto (fun m : ℕ => itoGridError B C T K K₂ (T / (m : ℝ)))
      Filter.atTop (𝓝 0) := by
  have hx : Filter.Tendsto (fun m : ℕ => T / (m : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hcomp := ((continuous_itoGridError B C T K K₂).tendsto 0).comp hx
  rwa [itoGridError_zero] at hcomp

section Formula

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in
/-- **The `L¹` defect of Itô's formula on a uniform grid.** -/
theorem IsItoVersion.integral_abs_itoFormula_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hX₀ : Measurable X₀) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {K₁ K₂ : ℝ} (hf'bd : ∀ x, |f' x| ≤ K₁) (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ x, |f'' x| ≤ K₂)
    {K : ℝ} (hK0 : 0 ≤ K) (hf''lip : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    (hmg : Measurable (Function.uncurry fun ω s => f' (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => f' (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖f' (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
          + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)) P
      ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
            + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                hmg hpg hqg T ω
            + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P
        ≤ itoGridError B C T K K₂ (T / (m : ℝ)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hf'd : Differentiable ℝ f' := fun x => (hf' x).differentiableAt
  have hf'c : Continuous f' := hf'd.continuous
  have hf''c : Continuous f'' := by
    have hlip : LipschitzWith (Real.toNNReal K) f'' := by
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0]
      exact hf''lip u v
    exact hlip.continuous
  have hf'lip : ∀ u v : ℝ, |f' u - f' v| ≤ K₂ * |u - v| :=
    abs_sub_le_of_hasDerivAt_bound hf' hf''bd
  -- the four error terms
  obtain ⟨hZ1int, hZ1le⟩ := integral_abs_taylorRemainder_le W ℱ hℱ H hm hp hq hC0 hCH hX₀
    bdrift hbm hB0 hB hK0 hf hf' hf''lip hT hm0
  obtain ⟨hZ2int, hZ2le⟩ := h.integral_abs_frozenRiemann_sub_le hC0 hCH hbm hB0 hB
    bdrift hbm hB0 hB hf'c hf'bd hK₂0 hf'lip hT hm0
  have hZ3sq := h.lintegral_sq_martingaleRiemann_sub_le hC0 hCH hbm hB0 hB hf'bd hK₂0 hf'lip
    hmg hpg hqg hT hm0
  obtain ⟨hZ4int, hZ4le⟩ := h.integral_abs_quadVarRiemann_sub_le hC0 hCH hbm hB0 hB
    hf''c hK₂0 hf''bd hK0 hf''lip hT hm0
  -- the martingale term in `L¹`
  have hZ3meas : Measurable fun ω : Ω => (∑ i : Fin m, f' (X (unifGrid T m (i : ℕ)) ω)
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω := by
    refine Measurable.sub (Finset.measurable_sum _ fun i _ =>
      (hf'c.measurable.comp (h.measurable (unifGrid T m (i : ℕ)))).mul
        (measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq _ _)) ?_
    exact ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ
      (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T).mono (ℱ.le T)).measurable
  have hV0 : (0 : ℝ) ≤ C ^ 2 * (K₂ ^ 2 * (T * (2 * (B * (T / (m : ℝ))) ^ 2
      + 2 * (C ^ 2 * (T / (m : ℝ)))))) := by
    have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
    have hT0 : (0 : ℝ) ≤ T := hT.le
    positivity
  obtain ⟨hZ3int, hZ3le⟩ := integral_abs_le_sqrt_of_lintegral_sq_le
    hZ3meas.aestronglyMeasurable hV0 (by
      refine hZ3sq.trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)])
  -- the increments split
  have hsub : ∀ᵐ ω ∂P, ∀ i : ℕ,
      X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω
        = (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω) :=
    MeasureTheory.ae_all_iff.mpr fun i => h.sub_ae hbm hB (unifGrid_nonneg hT.le m i)
      (unifGrid_lt_succ hT hm0 i).le
  have hgrid : ∀ᵐ ω ∂P, ∀ i : ℕ, X (unifGrid T m i) ω
      = itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω :=
    h.ae_eq_all (unifGrid T m) fun i => unifGrid_nonneg hT.le m i
  -- the Taylor remainder transferred to the version
  have hRae : (fun ω : Ω => taylorRemainder f f' f''
        (fun i => X (unifGrid T m i) ω) m)
      =ᵐ[P] fun ω => taylorRemainder f f' f''
        (fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω) m := by
    filter_upwards [hgrid] with ω hω
    have hfun : (fun i => X (unifGrid T m i) ω)
        = fun i => itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (unifGrid T m i) ω := funext hω
    rw [hfun]
  have hZ1int' : MeasureTheory.Integrable (fun ω : Ω =>
      taylorRemainder f f' f'' (fun i => X (unifGrid T m i) ω) m) P := hZ1int.congr hRae.symm
  have hZ1le' : ∫ ω, |taylorRemainder f f' f'' (fun i => X (unifGrid T m i) ω) m| ∂P
      ≤ K * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ))))) :=
    le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hRae.fun_comp abs))) hZ1le
  -- the halved quadratic-variation term
  have hZ4le' : ∫ ω, |1 / 2 * ((∑ i ∈ Finset.range m, f'' (X (unifGrid T m i) ω)
          * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
        - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P
      ≤ 1 / 2 * ((m : ℝ) * (K₂ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (2 * K₂ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))))
        + Real.sqrt (K₂ ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
            * ((m : ℝ) * (T / (m : ℝ)) ^ 2))
        + K * C ^ 2 * (T * (B * (T / (m : ℝ)) + C * Real.sqrt (T / (m : ℝ))))) := by
    have habs : ∀ ω : Ω, |1 / 2 * ((∑ i ∈ Finset.range m, f'' (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
          - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)|
        = 1 / 2 * |(∑ i ∈ Finset.range m, f'' (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
          - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume| := by
      intro ω
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp_rw [habs]
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hZ4le (by norm_num)
  -- the grid decomposition
  have hdecomp : (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
          + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume))
      =ᵐ[P] fun ω => taylorRemainder f f' f'' (fun i => X (unifGrid T m i) ω) m
        + ((∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + ((∑ i : Fin m, f' (X (unifGrid T m (i : ℕ)) ω)
              * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                  (unifGrid T m ((i : ℕ) + 1)) ω
                - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
            - stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                hmg hpg hqg T ω)
        + 1 / 2 * ((∑ i ∈ Finset.range m, f'' (X (unifGrid T m i) ω)
              * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2)
            - ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume) := by
    filter_upwards [hsub] with ω hω
    have hfin : (∑ i : Fin m, f' (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
        = ∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω) :=
      Fin.sum_univ_eq_sum_range (fun i => f' (X (unifGrid T m i) ω)
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω)) m
    rw [hfin]
    simp only [taylorRemainder, unifGrid_self hm0, unifGrid_zero]
    have hsplit : ∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
        * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω)
        = (∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume)
          + ∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
            * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
              - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hω i]
      ring
    have hhalf : ∑ i ∈ Finset.range m, f'' (X (unifGrid T m i) ω)
        * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2 / 2
        = 1 / 2 * ∑ i ∈ Finset.range m, f'' (X (unifGrid T m i) ω)
            * (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hhalf]
    ring
  refine ⟨(((hZ1int'.add hZ2int).add hZ3int).add (hZ4int.const_mul (1 / 2))).congr
      hdecomp.symm, ?_⟩
  refine le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hdecomp.fun_comp abs))) ?_
  -- the mesh identities
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have e1 : (m : ℝ) * (B * (T / (m : ℝ))) ^ 3 = B ^ 3 * T * (T / (m : ℝ)) ^ 2 := by
    field_simp
  have e2 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ))) ^ 2)
      = K₂ * (B ^ 2 * T * (T / (m : ℝ))) := by
    field_simp
  have e3 : (m : ℝ) * (2 * K₂ * (B * (T / (m : ℝ))) * (C * Real.sqrt (T / (m : ℝ))))
      = 2 * K₂ * B * C * T * Real.sqrt (T / (m : ℝ)) := by
    field_simp
  have e4 : (m : ℝ) * (T / (m : ℝ)) ^ 2 = T * (T / (m : ℝ)) := by
    field_simp
  rw [e1] at hZ1le'
  rw [e2, e3, e4] at hZ4le'
  unfold itoGridError
  exact integral_abs_add_four_le hZ1int' hZ2int hZ3int (hZ4int.const_mul (1 / 2))
    hZ1le' hZ2le hZ3le hZ4le'

include hC0 hCH in
/-- **Itô's formula for a scalar Itô process.** For a continuous adapted version `X` of
`X₀ + ∫ b ds + ∫ H dW` with bounded coefficients, and `f` twice differentiable with bounded
derivatives and Lipschitz second derivative,

  `f(X_T) − f(X_0) = ∫_0^T f'(X_s) b_s ds + ∫_0^T f'(X_s) H_s dW_s
      + ½ ∫_0^T f''(X_s) H_s² ds`

almost surely. -/
theorem IsItoVersion.itoFormula
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hX₀ : Measurable X₀) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    {K₁ K₂ : ℝ} (hf'bd : ∀ x, |f' x| ≤ K₁) (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ x, |f'' x| ≤ K₂)
    {K : ℝ} (hK0 : 0 ≤ K) (hf''lip : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|)
    (hmg : Measurable (Function.uncurry fun ω s => f' (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => f' (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖f' (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω =>
      (∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume := by
  have hgrid : ∀ m : ℕ, m ≠ 0 →
      MeasureTheory.Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
          - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
            + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                hmg hpg hqg T ω
            + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)) P
        ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
            - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
              + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s)
                  hmg hpg hqg T ω
              + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P
          ≤ itoGridError B C T K K₂ (T / (m : ℝ)) := fun m hm0 =>
    h.integral_abs_itoFormula_le hC0 hCH hX₀ hbm hB0 hB hf hf' hf'bd hK₂0 hf''bd hK0
      hf''lip hmg hpg hqg hT hm0
  obtain ⟨hZint, -⟩ := hgrid 1 one_ne_zero
  have hzero : ∫ ω, |f (X T ω) - f (X 0 ω)
      - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P ≤ 0 := by
    refine ge_of_tendsto (tendsto_itoGridError B C T K K₂) ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with m hmpos
    exact (hgrid m hmpos.ne').2
  have hnn : (0 : ℝ) ≤ ∫ ω, |f (X T ω) - f (X 0 ω)
      - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume)| ∂P :=
    MeasureTheory.integral_nonneg fun ω => abs_nonneg _
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg
    (fun ω => abs_nonneg _) hZint.abs).mp (le_antisymm hzero hnn)
  filter_upwards [hae] with ω hω
  have hz : f (X T ω) - f (X 0 ω)
      - ((∫ s in Set.Ioc (0 : ℝ) T, f' (X s ω) * bdrift ω s ∂volume)
        + stochasticIntegralBrownian W ℱ hℱ (fun ω s => f' (X s ω) * H ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T, f'' (X s ω) * H ω s ^ 2 ∂volume) = 0 :=
    abs_eq_zero.mp hω
  linarith

end Formula

end LevyStochCalc.Brownian.Ito
